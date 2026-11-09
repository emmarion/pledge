import type { Span } from "./syntax.ts";
import type { Rendered } from "./api.ts";
import { addRule, app, canon, create, entry, identical, occurs, ref, rewrites, same, sameHead, subst,
  typeOf } from "./terms.ts";
import type { App, Binder, EntryId, Fresh, Head, OpenTerm, Ref, Scope, Signature, Telescope, Term } from "./terms.ts";
import { cat, entryRef, join, render } from "./render.ts";
import { unfolds } from "./context.ts";

interface Opened { scope: Scope; entries: EntryId[]; env: Term[] }

export function open(scope: Scope, tele: Telescope, env: readonly Term[],
    fresh: (b: Binder, i: number) => Fresh): Opened {
  const out: Opened = { scope, entries: [], env: [...env] };
  tele.forEach((b, i) => {
    const f = fresh(b, i);
    const made = create(out.scope, subst(b.type, out.env), b.is && subst(b.is, out.env),
      { ...f, erased: f.erased ?? b.mult === "erased" });
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

type Why = "scrutinee" | "scrutinee type" | "types" | { head: Head; index: number };
interface Eq { lhs: Term; rhs: Term; why: Why; parent: Seen | null }
interface Seen extends Eq { scope: Scope; l: Term; r: Term; gave: { x: EntryId; e: Term } | null }
type Clash = { heads: readonly [Head, Head] } | { x: EntryId; e: Term } | { rigid: readonly [Term, Term] };
interface Failed { eq: Seen; failure: Clash; log: readonly Seen[] }

export type Forced = { ok: true; scope: Scope; fields: EntryId[] } | { ok: false; derivation: () => Rendered[] };

function orient(l: Term, r: Term, may: (id: EntryId) => boolean): { x: Ref; e: Term }
    | { apps: readonly [App, App] } | null {
  if (l.tag === "app" && r.tag === "app") return { apps: [l, r] };
  const x = [l, r].reduce<Ref | null>((best, t) =>
    t.tag === "entry" && may(t.id) && (!best || t.id > best.id) ? t : best, null);
  return x && { x, e: x === l ? r : l };
}

function solve(scope: Scope, eqs: Eq[], at: Span,
    may: (id: EntryId) => boolean): { scope: Scope; failed: Failed | null } {
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
    now = addRule(now, o.x.id, o.e, at);
    eqs.push({ lhs: entry(now, o.x.id).type, rhs: typeOf(now, o.e), why: "types", parent: e });
  }
  return { scope: now, failed: null };
}

export function unify(scope: Scope, lhs: Term, rhs: Term, at: Span,
    hole: (id: EntryId) => boolean): { scope: Scope; stuck: readonly [Term, Term] | null } {
  const { scope: now, failed } = solve(scope, [{ lhs, rhs, why: "types", parent: null }], at, hole);
  return { scope: now, stuck: failed && "rigid" in failed.failure ? failed.failure.rigid : null };
}

export function force(scope: Scope, scrutinee: EntryId, ctor: Signature, at: Span,
    fresh: (b: Binder, i: number) => Fresh): Forced {
  const opened = open(scope, ctor.params, [], fresh);
  const { scope: now, failed } = solve(opened.scope, [
    { lhs: ref(scrutinee), rhs: app(ctor.head, ...opened.env), why: "scrutinee", parent: null },
    { lhs: entry(opened.scope, scrutinee).type, rhs: subst(ctor.ret, opened.env), why: "scrutinee type", parent: null },
  ], at, () => true);
  return failed ? { ok: false, derivation: () => derivation(ctor, failed) }
    : { ok: true, scope: now, fields: opened.entries };
}

function derivation(ctor: Signature, { eq: failing, failure, log }: Failed): Rendered[] {
  const adder = (id: EntryId): Seen | undefined => log.find(s => s.gave?.x === id);
  const used = ({ scope, lhs, rhs }: Seen): EntryId[] =>
    [...new Set([...rewrites(scope, lhs), ...rewrites(scope, rhs)].map(s => s.by))]
      .filter(id => adder(id) || !unfolds(scope, id));
  const shown = new Set<Seen>();
  const show = (s: Seen | null | undefined): void => {
    if (!s || shown.has(s)) return;
    shown.add(s);
    show(s.parent);
    used(s).forEach(id => show(adder(id)));
  };
  show(failing);
  const listed = log.filter(s => shown.has(s)), num = (s: Seen | null | undefined) => listed.indexOf(s!) + 1;
  const lines = listed.map(s => {
    const { scope, l, r, why, parent, gave } = s, term = (t: Term) => render(scope, t, { canonical: false });
    const reason = why === "scrutinee" ? `forcing ${ctor.head.name} on the scrutinee`
      : why === "scrutinee type" ? `the scrutinee's type and ${ctor.head.name}'s`
      : why === "types" ? `the types of the two sides of ${num(parent)}`
      : `argument ${why.index + 1} of ${why.head.name} in ${num(parent)}`;
    const rules = used(s).map(id => { const from = adder(id);
      return from ? cat(entryRef(scope, id), `, from ${num(from)}`) : entryRef(scope, id); });
    return cat(`${num(s)}. `, term(l), " = ", term(r), `   (${reason}`,
      ...(rules.length ? ["; rewritten by ", ...join(rules, ", ")] : []), ")",
      ...(gave ? [", so ", entryRef(scope, gave.x), " is ", term(gave.e)] : []));
  });
  const { scope } = failing;
  return [...lines, "heads" in failure
    ? cat(`refuted: ${failure.heads[0].name} and ${failure.heads[1].name} are different heads`)
    : "rigid" in failure ? cat("refuted: ", ...join(failure.rigid.map(t => render(scope, t, { canonical: false })),
      " and "), " cannot be equated")
    : cat("refuted: ", entryRef(scope, failure.x), " occurs strictly inside ",
      render(scope, failure.e, { canonical: false }))];
}
