import type { CheckResult, EntryInfo, ExpectedEntry, ExpectedInfo, GlobalInfo, PositionInfo, Rendered } from "./api.ts";
import { bound, entries, entry, mapLeaves } from "./terms.ts";
import type { Entry, OpenTerm, Scope, Signature, Term } from "./terms.ts";
import { canonicalOf, cat, entryInfo, explain, render, renderTelescope } from "./render.ts";
import { parseExpr } from "./parser.ts";
import { attempt, globalAt, innermost, written } from "./context.ts";
import type { Declared, Given, Global, Local, Snapshot, State } from "./context.ts";
import { closed, single } from "./expr.ts";
import type { Phase } from "./syntax.ts";

const shift = (t: OpenTerm, env: readonly Term[]): OpenTerm =>
  mapLeaves(t, u => u.tag === "bound" ? env[u.index] ?? bound(u.index - env.length) : u);

function expectedEntries(scope: Scope, given: Given): ExpectedEntry[] {
  const bound = given.wants.map(w => w.name), at = (t: OpenTerm) => shift(t, given.env);
  const raw = (t: OpenTerm) => render(scope, at(t), { canonical: false, bound });
  const canonical = (t: OpenTerm) => canonicalOf(scope, at(t), bound);
  return given.wants.map(w => ({ name: w.name, type: w.type && raw(w.type), rule: w.is && raw(w.is),
    canonical: { type: w.type && canonical(w.type), rule: w.is && canonical(w.is) },
    undetermined: w.type === null, erased: w.mult === "erased" }));
}

function expected(scope: Scope, given: Given | null): ExpectedInfo {
  if (!given) return { entries: null };
  const entries = expectedEntries(scope, given);
  return given.params === undefined ? { entries } : { params: entries.slice(0, given.params),
    entries: entries.slice(given.params) };
}

const signatureOf = (scope: Scope, sig: Signature, erased = false): Rendered =>
  cat(renderTelescope(scope, sig.params, [], false, erased),
    " : ", render(scope, sig.ret, { canonical: false, bound: sig.params.map(b => b.name) }));

const declared = (scope: Scope, g: Declared, phase: Phase = 1): Rendered => g.kind !== "fn"
  ? signatureOf(scope, g.sig, g.kind === "type" && phase === 2)
  : g.sig ? cat(renderTelescope(scope, g.sig.params, [], false), " -> ",
    renderTelescope(scope, g.sig.returns, g.sig.params.map(b => b.name), false))
  : cat("(...)");

function globalInfo(scope: Scope, g: Global, st: State, limit: number): GlobalInfo[] {
  switch (g.kind) {
    case "ctor": return [];
    case "fn": return [{ kind: "fn", name: g.name, at: g.at, signature: declared(scope, g, st.phase) }];
    case "type": {
      const ctors = (g.ctors ?? []).flatMap(name => {
        const c = globalAt(st, limit, name);
        return c?.kind === "ctor" ? [{ name, at: c.sig.at ?? null, signature: signatureOf(scope, c.sig) }] : [];
      });
      return [{ kind: "type", name: g.name, at: g.sig.at ?? null, signature: declared(scope, g, st.phase),
        ...(g.ctors ? { ctors } : {}) }];
    }
    case "binding": return [];
  }
}

function scoped({ scope, tainted, erased }: Local, e: Entry): EntryInfo {
  return { ...entryInfo(scope, e.id, false), tainted: e.names.filter(n => tainted.has(n)),
    erased: e.erased || (e.names.length > 0 && e.names.every(n => erased.has(n))) };
}

export function info(st: State, snap: Snapshot): PositionInfo {
  const { scope } = snap.local, all = entries(scope).map(e => scoped(snap.local, e));
  const global = (e: EntryInfo): boolean => snap.decl === null || e.id < snap.decl;
  return {
    expected: expected(scope, snap.given),
    termination: snap.fn?.info ?? null,
    scope: all.filter(e => !global(e)),
    globalEntries: all.filter(global),
    topLevel: snap.decl === null,
    taintedBy: snap.local.taintedBy,
    refutations: snap.refutations,
    globals: st.globals.slice(0, snap.limit).flatMap(g => globalInfo(scope, g, st, snap.limit)),
  };
}

export function queries(st: State, fallback: (offset: number) => Snapshot):
    Pick<CheckResult, "infoAt" | "nameAt" | "usesAt" | "explainAt" | "evalAt"> {
  const at = (offset: number): Snapshot => innermost(st.snapshots, offset) ?? fallback(offset);
  return {
    infoAt: offset => info(st, at(offset)),
    nameAt: offset => {
      const o = innermost(st.occurrences, offset);
      if (!o) return null;
      const { local, of, def } = o;
      return typeof of === "number" ? { kind: "entry", entry: scoped(local, entry(local.scope, of)), def }
        : { kind: of.kind, name: of.name, signature: declared(local.scope, of), def };
    },
    usesAt: offset => {
      const def = innermost(st.occurrences, offset)?.def;
      if (!def) return null;
      const uses = new Map(st.occurrences.filter(o => o.def?.start === def.start && o.span.start !== def.start)
        .map(o => [o.span.start, o.span]));
      return [...uses.values()].sort((a, b) => a.start - b.start);
    },
    explainAt: offset => {
      const p = innermost(st.explains, offset);
      return p ? { span: p.span, ...("wants" in p.of ? { stands: expectedEntries(p.scope, p.of) }
        : explain(p.scope, written(p.scope, p.of))) } : null;
    },
    evalAt: (offset, text) => {
      const parsed = parseExpr(text, st.phase);
      if ("error" in parsed) return parsed;
      const snap = at(offset);
      return attempt(() => {
        const out = closed({ st: { ...st, record: false, table: new Map() }, fn: snap.fn, skeleton: false,
          limit: snap.limit, erased: true, inType: false, holes: [], decl: snap.decl }, snap.local, parsed.expr, null);
        const scope = out.local.scope, e = entry(scope, single(out, parsed.expr.span).id);
        const both = (t: Term): [Rendered, Rendered] => [render(scope, written(scope, t), { canonical: false }),
          render(scope, t)];
        const [type, canonicalType] = both(e.type), rule = e.rule && both(e.rule.term);
        return { type, canonicalType, rule: rule?.[0] ?? null, canonicalRule: rule?.[1] ?? null };
      });
    },
  };
}
