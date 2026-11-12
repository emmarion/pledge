import type { Span } from "./syntax.ts";
import type { Rendered } from "./api.ts";
import { addRule, app, canon, create, entry, identical, occurs, ref, rewrites, same, sameHead, subst,
  typeOf, withName } from "./terms.ts";
import type { App, Binder, EntryId, Fresh, Head, OpenTerm, Ref, Scope, Signature, Telescope, Term } from "./terms.ts";
import { cat, entryRef, join, render } from "./render.ts";

interface Opened { scope: Scope; entries: EntryId[]; env: Term[] }

export function open(scope: Scope, tele: Telescope, env: readonly Term[],
    fresh: (b: Binder, i: number) => Fresh): Opened {
  const out: Opened = { scope, entries: [], env: [...env] };
  tele.forEach((b, i) => {
    const f = fresh(b, i);
    const made = create(out.scope, subst(b.type, out.env), b.is && subst(b.is, out.env),
      { ...f, erased: f.erased ?? b.mult === "erased" }, b.span);
    out.scope = made.scope;
    out.entries.push(made.id);
    out.env.push(ref(made.id));
  });
  return out;
}

export function difference(scope: Scope, a: Telescope, b: Telescope): number {
  const agree = (x: OpenTerm | null, y: OpenTerm | null): boolean => x === null || y === null ? x === y
    : identical(scope, x, y);
  const i = a.findIndex((x, j) => { const y = b[j]; return !y || x.mult !== y.mult || !agree(x.type, y.type)
    || !agree(x.is, y.is); });
  return i >= 0 ? i : a.length < b.length ? a.length : -1;
}

type Why = "scrutinee" | "scrutinee type" | "types" | "hole" | { head: Head; index: number };
interface Eq { lhs: Term; rhs: Term; why: Why; parent: Seen | null }
interface Seen extends Eq { scope: Scope; l: Term; r: Term; gave: { x: EntryId; e: Term } | null }
type Clash = { heads: readonly [Head, Head] } | { x: EntryId; e: Term } | { rigid: readonly [Term, Term] };
interface Failed { eq: Seen; failure: Clash; log: readonly Seen[] }
interface Forcing { ctor: Signature; fields: readonly Term[]; scrutinee: EntryId; site: string }

export type Forced = { ok: true; scope: Scope; fields: EntryId[] } | { ok: false; derivation: () => Rendered[] };

function orient(l: Term, r: Term, may: (id: EntryId) => boolean): { x: Ref; e: Term }
    | { apps: readonly [App, App] } | null {
  if (l.tag === "app" && r.tag === "app") return { apps: [l, r] };
  const x = [l, r].reduce<Ref | null>((best, t) =>
    t.tag === "entry" && may(t.id) && (!best || t.id > best.id) ? t : best, null);
  return x && { x, e: x === l ? r : l };
}

function solve(scope: Scope, eqs: Eq[], at: Span, may: (id: EntryId) => boolean,
    forcing: Forcing | null): { scope: Scope; failed: Failed | null } {
  let now = scope;
  const log: Seen[] = [];
  for (const eq of eqs) {
    const e: Seen = { ...eq, scope: now, l: canon(now, eq.lhs), r: canon(now, eq.rhs), gave: null };
    log.push(e);
    const failed = (failure: Clash) => ({ scope: now, failed: { eq: e, failure, log } });
    if (same(e.l, e.r)) continue;
    const o = orient(e.l, e.r, may);
    if (!o) return failed({ rigid: [e.l, e.r] });
    if ("apps" in o) {
      const [a, b] = o.apps;
      if (!sameHead(a.head, b.head) || a.args.length !== b.args.length) return failed({ heads: [a.head, b.head] });
      a.args.forEach((lhs, index) => { const rhs = b.args[index]; if (rhs) eqs.push({ lhs, rhs,
        why: { head: a.head, index }, parent: e }); });
      continue;
    }
    if (occurs(o.x.id, o.e)) return failed({ x: o.x.id, e: o.e });
    e.gave = { x: o.x.id, e: o.e };
    now = addRule(now, o.x.id, o.e, at, view => lines(forcing, log, e, view));
    eqs.push({ lhs: entry(now, o.x.id).type, rhs: typeOf(now, o.e), why: "types", parent: e });
  }
  return { scope: now, failed: null };
}

export function unify(scope: Scope, lhs: Term, rhs: Term, at: Span,
    hole: (id: EntryId) => boolean): { scope: Scope; stuck: readonly [Term, Term] | null } {
  const { scope: now, failed } = solve(scope, [{ lhs, rhs, why: "hole", parent: null }], at, hole, null);
  return { scope: now, stuck: !failed ? null : "x" in failed.failure ? [ref(failed.failure.x), failed.failure.e]
    : [failed.eq.l, failed.eq.r] };
}

export function force(scope: Scope, scrutinee: EntryId, ctor: Signature, at: Span, site: string,
    fresh: (b: Binder, i: number) => Fresh, shown: (b: Binder, i: number) => string | null): Forced {
  const opened = open(scope, ctor.params, [], fresh), forcing = { ctor, fields: opened.env, scrutinee, site };
  const solved = (from: Scope) => solve(from, [
    { lhs: ref(scrutinee), rhs: app(ctor.head, ...opened.env), why: "scrutinee", parent: null },
    { lhs: entry(from, scrutinee).type, rhs: subst(ctor.ret, opened.env), why: "scrutinee type", parent: null },
  ], at, () => true, forcing);
  const { scope: now, failed } = solved(opened.scope);
  const named = () => opened.entries.reduce((s, id, i) => {
    const name = shown(ctor.params[i]!, i);
    return name === null ? s : withName(s, id, name);
  }, opened.scope);
  return failed ? { ok: false, derivation: () => derivation(forcing, solved(named()).failed!) }
    : { ok: true, scope: now, fields: opened.entries };
}

function lines(forcing: Forcing | null, log: readonly Seen[], target: Seen, view: Scope | null): Rendered[] {
  const adder = (id: EntryId): Seen | undefined => log.find(s => s.gave?.x === id);
  const used = ({ scope, lhs, rhs }: Seen): EntryId[] =>
    [...new Set([...rewrites(scope, lhs), ...rewrites(scope, rhs)].map(s => s.by))];
  const shown = new Set<Seen>();
  const show = (s: Seen | null | undefined): void => {
    if (!s || shown.has(s)) return;
    shown.add(s);
    show(s.parent);
    used(s).forEach(id => show(adder(id)));
  };
  show(target);
  const listed = log.filter(s => shown.has(s)), num = (s: Seen | null | undefined) => listed.indexOf(s!) + 1;
  const shownLines = listed.map(s => {
    const { l, r, why, parent, gave } = s, scope = view ?? s.scope;
    const term = (t: Term) => render(scope, t, { canonical: false }), name = forcing?.ctor.head.name;
    const reason = why === "scrutinee" ? `forcing ${name} on the scrutinee`
      : why === "scrutinee type" ? `the scrutinee's type and ${name}'s`
      : why === "hole" ? "solving a `_` (§20)"
      : why === "types" ? `the types of the two sides of ${num(parent)}`
      : `argument ${why.index + 1} of ${why.head.name} in ${num(parent)}`;
    const rules = used(s).map(id => { const from = adder(id);
      return from ? cat(entryRef(scope, id), `, from ${num(from)}`) : entryRef(scope, id); });
    return cat(`${num(s)}. `, term(l), " = ", term(r), `   (${reason}`,
      ...(rules.length ? ["; rewritten by ", ...join(rules, ", ")] : []), ")",
      ...(gave ? [", so ", entryRef(scope, gave.x), " is ", term(gave.e)] : []));
  });
  return [...forcing ? [header(forcing, view ?? target.scope)] : [], ...shownLines];
}

const header = ({ ctor, fields, scrutinee, site }: Forcing, scope: Scope): Rendered => {
  const raw = (t: Term) => render(scope, t, { canonical: false });
  const pat = raw(app(ctor.head, ...fields)), s = entryRef(scope, scrutinee);
  return site.startsWith("match") ? cat(`${site} `, s, " { ", pat, " => ... }") : cat(`${site} `, pat, " = ", s, ";");
};

function derivation(forcing: Forcing, { eq: failing, failure, log }: Failed): Rendered[] {
  const { scope } = failing, [head, ...rest] = lines(forcing, log, failing, null);
  return [cat("suppose ", head!), ...rest, "heads" in failure
    ? cat(`refuted: ${failure.heads[0].name} and ${failure.heads[1].name} are different heads`)
    : "rigid" in failure ? cat("refuted: ", ...join(failure.rigid.map(t => render(scope, t, { canonical: false })),
      " and "), " cannot be equated")
    : cat("refuted: ", entryRef(scope, failure.x), " occurs strictly inside ",
      render(scope, failure.e, { canonical: false }))];
}
