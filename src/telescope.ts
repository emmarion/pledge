import type { Span } from "./syntax.ts";
import type { Rendered } from "./api.ts";
import { addRule, app, canon, create, entry, identical, occurs, ref, rewrites, same, sameHead, subst, typeOf } from "./terms.ts";
import type { App, Binder, EntryId, Fresh, Head, OpenTerm, Origin, Ref, Scope, Signature, Telescope, Term } from "./terms.ts";
import { cat, entryRef, join, render } from "./render.ts";

export interface Opened { scope: Scope; entries: EntryId[]; env: Term[] }

export function open(scope: Scope, tele: Telescope, env: readonly Term[], fresh: (b: Binder, i: number) => Fresh): Opened {
  const out: Opened = { scope, entries: [], env: [...env] };
  tele.forEach((b, i) => {
    const f = fresh(b, i);
    const made = create(out.scope, subst(b.type, out.env), b.is && subst(b.is, out.env), { ...f, erased: f.erased ?? b.mult === "erased" });
    out.scope = made.scope;
    out.entries.push(made.id);
    out.env.push(ref(made.id));
  });
  return out;
}

export interface Mismatch { index: number; kind: "arity" | "type" | "is"; message: () => string }
export type Instantiated = { ok: true; env: Term[] } | { ok: false; mismatch: Mismatch };

export function instantiate(scope: Scope, tele: Telescope, given: readonly EntryId[], env: readonly Term[] = []): Instantiated {
  if (given.length !== tele.length) {
    const message = () => `${tele.length} expected, ${given.length} given`;
    return { ok: false, mismatch: { index: Math.min(given.length, tele.length), kind: "arity", message } };
  }
  const out = [...env];
  for (const [index, b] of tele.entries()) {
    const id = given[index] ?? -1;
    const fail = (kind: "type" | "is", want: Term, have: Term): Instantiated => ({
      ok: false,
      mismatch: {
        index, kind,
        message: () => `${b.name ?? "_"} (position ${index + 1}): ${entryRef(scope, id).text} ${kind === "is" ? "is" : "has type"} ${render(scope, have).text}, not ${render(scope, want).text}`,
      },
    });
    const wantType = subst(b.type, out), haveType = entry(scope, id).type;
    if (!identical(scope, wantType, haveType)) return fail("type", wantType, haveType);
    const wantIs = b.is && subst(b.is, out);
    if (wantIs && !identical(scope, wantIs, ref(id))) return fail("is", wantIs, ref(id));
    out.push(ref(id));
  }
  return { ok: true, env: out };
}

export function difference(scope: Scope, a: Telescope, b: Telescope, origin: Origin): number {
  const { scope: s, env } = open(scope, a, [], () => ({ origin }));
  const same = (x: OpenTerm | null, y: OpenTerm | null): boolean => x === null || y === null ? x === y : identical(s, subst(x, env), subst(y, env));
  const i = a.findIndex((x, j) => { const y = b[j]; return !y || x.mult !== y.mult || !same(x.type, y.type) || !same(x.is, y.is); });
  return i >= 0 ? i : a.length < b.length ? a.length : -1;
}

export type Applied = { ok: true; scope: Scope; id: EntryId } | { ok: false; mismatch: Mismatch };

export function apply(scope: Scope, sig: Signature, args: readonly EntryId[], fresh: Fresh): Applied {
  const inst = instantiate(scope, sig.params, args);
  return inst.ok ? { ok: true, ...create(scope, subst(sig.ret, inst.env), app(sig.head, ...args.map(ref)), fresh) } : inst;
}

type Why = "scrutinee" | "scrutinee type" | "types" | { head: Head; index: number };
interface Eq { lhs: Term; rhs: Term; why: Why; parent: Seen | null }
interface Seen extends Eq { scope: Scope; l: Term; r: Term }
type Failure = { heads: readonly [Head, Head] } | { x: EntryId; e: Term } | { rigid: readonly [Term, Term] };

export type Forced = { ok: true; scope: Scope; fields: EntryId[] } | { ok: false; derivation: () => Rendered[] };

function orient(l: Term, r: Term, may: (id: EntryId) => boolean): { x: Ref; e: Term } | { apps: readonly [App, App] } | null {
  if (l.tag === "app" && r.tag === "app") return { apps: [l, r] };
  const x = [l, r].reduce<Ref | null>((best, t) => t.tag === "entry" && may(t.id) && (!best || t.id > best.id) ? t : best, null);
  return x && { x, e: x === l ? r : l };
}

function solve(scope: Scope, eqs: Eq[], at: Span, may: (id: EntryId) => boolean): { scope: Scope; failed: { eq: Seen; failure: Failure } | null } {
  let now = scope;
  for (const eq of eqs) {
    const e: Seen = { ...eq, scope: now, l: canon(now, eq.lhs), r: canon(now, eq.rhs) };
    const failed = (failure: Failure) => ({ scope: now, failed: { eq: e, failure } });
    if (same(e.l, e.r)) continue;
    const o = orient(e.l, e.r, may);
    if (!o) return failed({ rigid: [e.l, e.r] });
    if ("apps" in o) {
      const [a, b] = o.apps;
      if (!sameHead(a.head, b.head) || a.args.length !== b.args.length) return failed({ heads: [a.head, b.head] });
      a.args.forEach((lhs, index) => { const rhs = b.args[index]; if (rhs) eqs.push({ lhs, rhs, why: { head: a.head, index }, parent: e }); });
      continue;
    }
    if (occurs(o.x.id, o.e)) return failed({ x: o.x.id, e: o.e });
    now = addRule(now, o.x.id, o.e, at);
    eqs.push({ lhs: entry(now, o.x.id).type, rhs: typeOf(now, o.e), why: "types", parent: e });
  }
  return { scope: now, failed: null };
}

export function unify(scope: Scope, lhs: Term, rhs: Term, at: Span, hole: (id: EntryId) => boolean): { scope: Scope; stuck: readonly [Term, Term] | null } {
  const { scope: now, failed } = solve(scope, [{ lhs, rhs, why: "types", parent: null }], at, hole);
  return { scope: now, stuck: failed && "rigid" in failed.failure ? failed.failure.rigid : null };
}

export function force(scope: Scope, scrutinee: EntryId, ctor: Signature, at: Span, fresh: (b: Binder, i: number) => Fresh): Forced {
  const opened = open(scope, ctor.params, [], fresh);
  const { scope: now, failed } = solve(opened.scope, [
    { lhs: ref(scrutinee), rhs: app(ctor.head, ...opened.env), why: "scrutinee", parent: null },
    { lhs: entry(opened.scope, scrutinee).type, rhs: subst(ctor.ret, opened.env), why: "scrutinee type", parent: null },
  ], at, () => true);
  return failed ? { ok: false, derivation: () => derivation(ctor, failed.eq, failed.failure) } : { ok: true, scope: now, fields: opened.entries };
}

function derivation(ctor: Signature, failing: Seen, failure: Failure): Rendered[] {
  const chain: Seen[] = [];
  for (let e: Seen | null = failing; e; e = e.parent) chain.unshift(e);
  const lines = chain.map(({ scope, lhs, rhs, l, r, why }, n) => {
    const reason = why === "scrutinee" ? `forcing ${ctor.head.name} on the scrutinee`
      : why === "scrutinee type" ? `the scrutinee's type and ${ctor.head.name}'s`
      : why === "types" ? `the types of the two sides of ${n}`
      : `argument ${why.index + 1} of ${why.head.name} in ${n}`;
    const used = [...new Set([...rewrites(scope, lhs), ...rewrites(scope, rhs)].map(s => s.by))];
    return cat(`${n + 1}. `, render(scope, l, { canonical: false }), " = ", render(scope, r, { canonical: false }), `   (${reason}`,
      ...(used.length ? ["; rewritten by ", ...join(used.map(id => entryRef(scope, id)), ", ")] : []), ")");
  });
  const { scope } = failing;
  return [...lines, "heads" in failure
    ? cat(`refuted: ${failure.heads[0].name} and ${failure.heads[1].name} are different heads`)
    : "rigid" in failure ? cat("refuted: ", ...join(failure.rigid.map(t => render(scope, t, { canonical: false })), " and "), " cannot be equated")
    : cat("refuted: ", entryRef(scope, failure.x), " occurs strictly inside ", render(scope, failure.e, { canonical: false }))];
}
