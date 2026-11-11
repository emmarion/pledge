import { test } from "node:test";
import assert from "node:assert/strict";
import {
  TYPE, abstract, app, bound, canon, create, declare, emptyScope, entries, entry, identical, isStrictSubterm, lookup, ref,
  rewrites, same, subst, withName,
} from "./terms.ts";
import type { Binder, Head, OpenTerm, Scope, Signature, Term } from "./terms.ts";
import { entryInfo, explain, render } from "./render.ts";
import { lineCol, position } from "./position.ts";
import { force, open } from "./telescope.ts";

const span = { start: 0, end: 0 };
const T = (name: string): Head => ({ kind: "type", name });
const C = (name: string): Head => ({ kind: "ctor", name });
const b = (name: string | null, type: OpenTerm, is: OpenTerm | null = null): Binder => ({ name, type, is, mult: "many", span });
const sig = (head: Head, params: Binder[], ret: OpenTerm = TYPE): Signature => ({ head, params, ret });
const id = (t: Term): number => t.tag === "entry" ? t.id : -1;
const fresh = (kind: string) => () => ({ origin: { kind, span } });

const Nat = app(T("Nat")), Zero = app(C("Zero"));
const Succ = <B,>(t: Term<B>) => app<B>(C("Succ"), t);
const sigs = {
  Nat: sig(T("Nat"), []),
  Zero: sig(C("Zero"), [], Nat),
  Succ: sig(C("Succ"), [b("pred", Nat)], Nat),
  Vec: sig(T("Vec"), [b("A", TYPE), b("n", Nat)]),
  VNil: sig(C("VNil"), [b("A", TYPE)], app(T("Vec"), bound(0), Zero)),
  VCons: sig(C("VCons"), [b("A", TYPE), b("n", Nat), b("head", bound(0)), b("rest", app(T("Vec"), bound(0), bound(1)))],
    app(T("Vec"), bound(0), Succ(bound(1)))),
  IsZero: sig(T("IsZero"), [b("n", Nat)]),
  IsZeroHere: sig(C("IsZeroHere"), [], app(T("IsZero"), Zero)),
  Eq: sig(T("Eq"), [b("a", Nat), b("b", Nat)]),
  Refl: sig(C("Refl"), [b("a", Nat)], app(T("Eq"), bound(0), bound(0))),
  Two: sig(T("Two"), []),
  MkTwo: sig(C("MkTwo"), [b("a", Nat), b("b", Nat)], app(T("Two"))),
};

function base(source = ""): Scope {
  return Object.values(sigs).reduce(declare, emptyScope(position(source)));
}

function add(scope: Scope, name: string | null, type: Term, rule: Term | null = null): [Scope, Term] {
  const made = create(scope, type, rule, { origin: { kind: "test", span } });
  return [name ? withName(made.scope, made.id, name) : made.scope, ref(made.id)];
}

function forced(scope: Scope, scrutinee: Term, ctor: Signature, names: string[] = []) {
  const r = force(scope, id(scrutinee), ctor, span, "match", fresh("field"), b => `@${b.name}`);
  if (!r.ok) return r;
  const named = r.fields.reduce((s, id, i) => names[i] ? withName(s, id, names[i]) : s, r.scope);
  return { ...r, scope: named, fields: r.fields.map(ref) };
}

const text = (scope: Scope, t: Term) => render(scope, t).text;

test("canonicalization rewrites to a fixed point", () => {
  let s = base(), x, y, z;
  [s, x] = add(s, "x", Nat);
  [s, y] = add(s, "y", Nat, Succ(x));
  [s, z] = add(s, "z", Nat, Succ(y));
  assert.ok(same(canon(s, z), Succ(Succ(x))));
  assert.equal(text(s, z), "Succ(Succ(x))");
  assert.equal(render(s, z, { canonical: false }).text, "z");
  assert.ok(identical(s, z, Succ(Succ(x))));
  assert.ok(!identical(s, z, Succ(x)));
});

test("opening a telescope gives each is binder's entry its rule", () => {
  const o = open(base(), [b("x", Nat), b("y", Nat, Succ(bound(0))), b("z", app(T("IsZero"), bound(1)))], [], fresh("param"));
  const [x, y, z] = o.entries;
  assert.ok(x !== undefined && y !== undefined && z !== undefined);
  assert.equal(entry(o.scope, x).rule, null);
  assert.ok(same(canon(o.scope, ref(y)), Succ(ref(x))));
  assert.ok(same(canon(o.scope, entry(o.scope, z).type), app(T("IsZero"), Succ(ref(x)))));
  assert.ok(same(abstract(o.scope, entry(o.scope, z).type, o.entries), app(T("IsZero"), bound(1))));
});

test("abstract unfolds application entries that mention the telescope's entries", () => {
  let s = base(), x, a;
  [s, x] = add(s, "x", Nat);
  [s, a] = add(s, null, Nat, Succ(x));
  assert.ok(same(abstract(s, app(T("IsZero"), a), [id(x)]), app(T("IsZero"), Succ(bound(0)))));
});

test("abstract leaves no entry made while checking the telescope, so the result outlives that scope", () => {
  const top = base();
  const o = open(top, [b("A", TYPE)], [], fresh("param"));
  const zero = create(o.scope, Nat, Zero, fresh("app")());
  const ret = abstract(zero.scope, app(T("Vec"), ref(o.entries[0] ?? -1), ref(zero.id)), o.entries);
  assert.ok(same(ret, app(T("Vec"), bound(0), Zero)));
  assert.equal(render(top, subst(ret, [Nat])).text, "Vec(Nat(), Zero())");
});

test("rewrite sequences have one step per rule and reach the canonical form", () => {
  let s = base(), y, x;
  [s, y] = add(s, "y", Nat, Zero);
  [s, x] = add(s, "x", Nat, Succ(y));
  const t = app(C("MkTwo"), x, y);
  const steps = rewrites(s, t);
  assert.deepEqual(steps.map(st => st.by), [x, y].map(r => id(r)));
  assert.ok(same(steps.at(-1)?.to ?? t, canon(s, t)));
  const ex = explain(s, t);
  assert.equal(ex.canonical.text, "MkTwo(Succ(Zero()), Zero())");
  assert.deepEqual(ex.rewrites.map(r => r.to.text), ["MkTwo(Succ(y), y)", "MkTwo(Succ(Zero()), Zero())"]);
  assert.equal(rewrites(s, Nat).length, 0);
});

test("forcing VCons on v : Vec(A, Succ(n)) equates the arguments one by one", () => {
  let s = base(), A, n, v;
  [s, A] = add(s, "A", TYPE);
  [s, n] = add(s, "n", Nat);
  [s, v] = add(s, "v", app(T("Vec"), A, Succ(n)));
  const r = forced(s, v, sigs.VCons, ["A2", "n2", "hd", "tl"]);
  assert.ok(r.ok);
  if (!r.ok) return;
  const [A2, n2, hd, tl] = r.fields;
  assert.ok(A2 && n2 && hd && tl);
  assert.ok(identical(r.scope, A2, A));
  assert.ok(identical(r.scope, n2, n));
  assert.equal(text(r.scope, entry(r.scope, id(A2)).type), "Type()");
  assert.equal(text(r.scope, v), "VCons(A, n, hd, tl)");
  assert.equal(text(r.scope, entry(r.scope, id(tl)).type), "Vec(A, n)");
  assert.equal(text(r.scope, entry(r.scope, id(hd)).type), "A");
});

test("forcing VNil on v : Vec(A, Succ(n)) is refuted by different heads", () => {
  let s = base(), A, n, v;
  [s, A] = add(s, "A", TYPE);
  [s, n] = add(s, "n", Nat);
  [s, v] = add(s, "v", app(T("Vec"), A, Succ(n)));
  const r = forced(s, v, sigs.VNil);
  assert.ok(!r.ok);
  if (r.ok) return;
  const lines = r.derivation().map(l => l.text);
  assert.equal(lines.at(-1), "refuted: Succ and Zero are different heads");
  assert.match(lines.at(-2) ?? "", /^2\. Succ\(n\) = Zero\(\)/);
});

test("IsZeroHere is refuted against IsZero(Succ(m)) in the Succ branch only", () => {
  let s = base(), n, p;
  [s, n] = add(s, "n", Nat);
  [s, p] = add(s, "p", app(T("IsZero"), n));
  const zero = forced(s, n, sigs.Zero);
  assert.ok(zero.ok);
  if (zero.ok) assert.ok(forced(zero.scope, p, sigs.IsZeroHere).ok);
  const succ = forced(s, n, sigs.Succ, ["m"]);
  assert.ok(succ.ok);
  if (!succ.ok) return;
  const r = forced(succ.scope, p, sigs.IsZeroHere);
  assert.ok(!r.ok);
  if (r.ok) return;
  const d = r.derivation();
  assert.deepEqual(d.map(l => l.text), [
    "suppose match p { IsZeroHere() => ... }",
    "1. IsZero(Succ(m)) = IsZero(Zero())   (the scrutinee's type and IsZeroHere's; rewritten by n)",
    "2. Succ(m) = Zero()   (argument 1 of IsZero in 1)",
    "refuted: Succ and Zero are different heads",
  ]);
  const nRef = d[1]?.refs.find(x => "entry" in x && x.entry === id(n));
  assert.ok(nRef);
  assert.equal(d[1]?.text.slice(nRef.span.start, nRef.span.end), "n");
  assert.equal(entry(s, id(n)).rule, null);
  assert.equal(entry(s, id(p)).rule, null);
  assert.equal(text(s, n), "n");
  assert.equal(entries(s).length, 2);
  assert.equal(lookup(s, "m"), undefined);
});

test("the occurs check refutes n = Succ(n)", () => {
  let s = base(), n, p;
  [s, n] = add(s, "n", Nat);
  [s, p] = add(s, "p", app(T("Eq"), n, Succ(n)));
  const r = forced(s, p, sigs.Refl);
  assert.ok(!r.ok);
  if (!r.ok) assert.equal(r.derivation().at(-1)?.text, "refuted: n occurs strictly inside Succ(n)");
});

test("when two entries are equated, the newer takes the rule", () => {
  let s = base(), x, y, p;
  [s, x] = add(s, "x", Nat);
  [s, y] = add(s, "y", Nat);
  [s, p] = add(s, "p", app(T("Eq"), x, y));
  const r = forced(s, p, sigs.Refl, ["a"]);
  assert.ok(r.ok);
  if (!r.ok) return;
  const [a] = r.fields;
  assert.equal(entry(r.scope, id(x)).rule, null);
  assert.ok(same(entry(r.scope, id(a ?? x)).rule?.term ?? Nat, x));
  assert.ok(same(entry(r.scope, id(y)).rule?.term ?? Nat, x));
  assert.equal(text(r.scope, p), "Refl(x)");
});

test("strict subterm in ack: m1 is a strict subterm of m once m is Succ(m1)", () => {
  let s = base(), m;
  [s, m] = add(s, "m", Nat);
  const r = forced(s, m, sigs.Succ, ["m1"]);
  assert.ok(r.ok);
  if (!r.ok) return;
  const [m1] = r.fields;
  assert.ok(m1);
  assert.ok(isStrictSubterm(r.scope, m1, m));
  assert.ok(!isStrictSubterm(r.scope, m, m1));
  assert.ok(!isStrictSubterm(r.scope, m1, m1));
  assert.ok(!isStrictSubterm(r.scope, m, m));
  assert.ok(isStrictSubterm(r.scope, m1, Succ(Succ(m1))));
  assert.ok(isStrictSubterm(s, m, Succ(m)) && !isStrictSubterm(s, m, Succ(Zero)));
});

test("anonymous entries render as markers with line and column, and refs locate entries", () => {
  const source = "fn f() -> (r : Nat()) {\n  g(Zero())\n}";
  let s = base(source), x;
  const at = source.indexOf("g(");
  assert.deepEqual(lineCol(source, at), { line: 2, col: 3 });
  const made = create(s, Nat, null, { origin: { kind: "call", span: { start: at, end: at + 9 } } });
  s = made.scope;
  [s, x] = add(s, "x", Nat, Succ(ref(made.id)));
  const r = render(s, app(C("MkTwo"), x, ref(made.id)));
  assert.equal(r.text, "MkTwo(Succ(?@2:3), ?@2:3)");
  assert.deepEqual(r.refs.map(q => r.text.slice(q.span.start, q.span.end)), ["?@2:3", "?@2:3"]);
  const info = entryInfo(s, id(x));
  assert.equal(info.type.text, "Nat()");
  assert.equal(info.rule?.text, "Succ(?@2:3)");
});
