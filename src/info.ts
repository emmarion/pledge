import type { CheckResult, ExpectedInfo, GlobalInfo, PositionInfo, Rendered } from "./api.ts";
import { bound, entries, entry, lookup } from "./terms.ts";
import type { OpenTerm, Scope, Term } from "./terms.ts";
import { cat, entryInfo, explain, render, renderTelescope } from "./render.ts";
import { parseExpr } from "./parser.ts";
import { APP, Failure, HOLE, innermost, isTainted, written } from "./context.ts";
import type { Given, Global, Snapshot, State } from "./context.ts";
import { expr, single } from "./expr.ts";

const shift = (t: OpenTerm, env: readonly Term[]): OpenTerm =>
  t.tag === "app" ? { ...t, args: t.args.map(a => shift(a, env)) } : t.tag === "bound" ? env[t.index] ?? bound(t.index - env.length) : t;

function expected(scope: Scope, given: Given | null): ExpectedInfo {
  if (!given) return { entries: null };
  const show = (t: OpenTerm) => render(scope, shift(t, given.env), { bound: given.wants.map(w => w.name) });
  const entries = given.wants.map(w => ({ name: w.name, type: w.type && show(w.type), rule: w.is && show(w.is), undetermined: w.type === null, erased: w.mult === "erased" }));
  return given.params === undefined ? { entries } : { params: entries.slice(0, given.params), entries: entries.slice(given.params) };
}

function globalInfo(scope: Scope, g: Global, st: State, limit: number): GlobalInfo[] {
  switch (g.kind) {
    case "ctor": return [];
    case "fn": {
      const sig = g.sig;
      return [{ kind: "fn", name: g.name, signature: sig
        ? cat(renderTelescope(scope, sig.params, [], false), " -> ", renderTelescope(scope, sig.returns, sig.params.map(b => b.name), false))
        : cat("(...)") }];
    }
    case "type": {
      const ctors = (g.ctors ?? []).flatMap(name => {
        const i = st.index.get(name), c = i !== undefined && i < limit ? st.globals[i] : undefined;
        return c?.kind === "ctor" ? [{ name, signature: cat(renderTelescope(scope, c.sig.params, [], false), " : ",
          render(scope, c.sig.ret, { canonical: false, bound: c.sig.params.map(b => b.name) })) }] : [];
      });
      return [{ kind: "type", name: g.name, signature: cat(renderTelescope(scope, g.sig.params, [], false), " : Type()"), ...(g.ctors ? { ctors } : {}) }];
    }
    case "binding": {
      const e = lookup(scope, g.name);
      return e?.id === g.id
        ? [{ kind: "binding", name: g.name, signature: cat(" : ", render(scope, e.type), ...(e.rule ? [" is ", render(scope, e.rule.term)] : [])) }]
        : [];
    }
  }
}

export function info(st: State, snap: Snapshot): PositionInfo {
  const { scope, tainted, erased } = snap.local;
  return {
    expected: snap.given === "none" ? null : expected(scope, snap.given),
    termination: snap.fn?.info ?? null,
    scope: entries(scope).filter(e => e.names.length || (e.origin.kind !== APP && e.origin.kind !== HOLE))
      .map(e => ({ ...entryInfo(scope, e.id), tainted: isTainted(e, tainted), erased: e.erased || (e.names.length > 0 && e.names.every(n => erased.has(n))) })),
    refutations: snap.refutations,
    globals: st.globals.slice(0, snap.limit).flatMap(g => globalInfo(scope, g, st, snap.limit)),
  };
}

export function queries(st: State, fallback: (offset: number) => Snapshot): Pick<CheckResult, "infoAt" | "explainAt" | "evalAt"> {
  const at = (offset: number): Snapshot => innermost(st.snapshots, offset) ?? fallback(offset);
  return {
    infoAt: offset => info(st, at(offset)),
    explainAt: offset => {
      const p = innermost(st.explains, offset);
      return p ? explain(p.scope, written(p.scope, p.term)) : null;
    },
    evalAt: (offset, text) => {
      const parsed = parseExpr(text, st.phase);
      if ("error" in parsed) return parsed;
      const snap = at(offset);
      try {
        const out = expr({ st: { ...st, record: false }, fn: snap.fn, skeleton: false, limit: snap.limit, erased: true, holes: [] }, snap.local, parsed.expr, null);
        const scope = out.local.scope, e = entry(scope, single(out, parsed.expr.span).id);
        const both = (t: Term): [Rendered, Rendered] => [render(scope, written(scope, t), { canonical: false }), render(scope, t)];
        const [type, canonicalType] = both(e.type), rule = e.rule && both(e.rule.term);
        return { type, canonicalType, rule: rule?.[0] ?? null, canonicalRule: rule?.[1] ?? null };
      } catch (err) {
        if (err instanceof Failure) return { error: err.diag };
        throw err;
      }
    },
  };
}
