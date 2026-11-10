import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { explainTerm, scopeOf, standsFor, verdicts } from "../../tests/helpers.ts";
import { page, program, run } from "../../tests/tutorial.ts";

const infoAt = (slug: string, learner: string, marker: string, nth = 0) => {
  const { source, r } = run(slug, learner);
  let at = source.length - learner.length + learner.indexOf("\n");
  for (let i = 0; i <= nth; i++) at = source.indexOf(marker, at + 1);
  assert.ok(at >= 0, marker);
  return { r, info: r.infoAt(at) };
};

const expectedAt = (slug: string, learner: string, marker: string, nth = 0): string =>
  infoAt(slug, learner, marker, nth).info.expected.entries!.map(e => `${e.name} : ${e.type!.text}`).join(", ");

const gaps: [string, string[]][] = [
  ["plus-zero", ["e : Eq(Nat(), Zero(), Zero())", "e : Eq(Nat(), Succ(r1), Succ(m))"]],
  ["vappend", ["r : Nat(), p : Plus(Zero(), n, r), u : Vec(A, r)", "r : Nat(), p : Plus(Succ(m1), n, r), u : Vec(A, r)"]],
  ["plus-succ", ["q : Plus(Zero(), Succ(n), Succ(n))", "q : Plus(Succ(m1), Succ(n), Succ(Succ(r1)))"]],
  ["plus-comm", ["q : Plus(n, Zero(), n)", "q : Plus(n, Succ(m1), Succ(r1))"]],
  ["plus-assoc", ["bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(Zero(), bc, r)"]],
  ["times-distrib", ["ab : Nat(), ac : Nat(), t1 : Times(Zero(), b, ab), t2 : Times(Zero(), c, ac), q : Plus(ab, ac, Zero())"]],
];

for (const [slug, expected] of gaps) test(`${slug}: the starting text checks with a sorry(_) in each gap the prose describes`, () => {
  const { initial } = page(slug);
  const { r } = run(slug, initial);
  assert.equal(r.error, null);
  assert.deepEqual(verdicts(r), [true, slug === "plus-zero" ? null : true, false]);
  assert.deepEqual(expected.map((_, i) => expectedAt(slug, initial, "sorry(_)", i)), expected);
});

test("plus-zero: in the Refl branch r1 is m, and the branch is tainted by the call while a sorry is left", () => {
  const learner = page("plus-zero").solution.replace("Refl(_, _) => Refl(Nat(), r)", "Refl(_, _) => sorry(_)");
  const { info } = infoAt("plus-zero", `--\n${learner}`, "sorry(_)");
  assert.equal(expectedAt("plus-zero", `--\n${learner}`, "sorry(_)"), "e : Eq(Nat(), Succ(m), Succ(m))");
  assert.ok(scopeOf(info).includes("r1 : Nat() is m"));
  assert.notEqual(info.taintedBy, null);
});

test("vappend: the gaps' scopes, the call bound with a sorry left, and each tuple element's Expected", () => {
  const { initial, solution } = page("vappend");
  const first = scopeOf(infoAt("vappend", initial, "sorry(_)").info);
  assert.ok(first.includes("m : Nat() is Zero()") && first.includes("v : Vec(A, Zero()) is VNil(A)"));
  const second = scopeOf(infoAt("vappend", initial, "sorry(_)", 1).info);
  for (const e of ["m : Nat() is Succ(m1)", "v : Vec(A, Succ(m1)) is VCons(A, m1, x, rest)", "x : A", "rest : Vec(A, m1)"])
    assert.ok(second.includes(e), e);
  const bound = solution.replace("(Succ(r1), PlusSucc(m1, n, r1, p1), VCons(A, r1, x, u1))", "sorry(_)");
  assert.deepEqual(verdicts(run("vappend", bound).r), [true, true, false]);
  const { info } = infoAt("vappend", bound, "sorry(_)");
  assert.ok(scopeOf(info).includes("p1 : Plus(m1, n, r1)") && scopeOf(info).includes("u1 : Vec(A, r1)"));
  assert.deepEqual(info.scope.filter(e => e.tainted.length).map(e => e.names), [["r1"], ["p1"], ["u1"]]);
  assert.deepEqual(["Succ(r1),", "PlusSucc(m1", "VCons(A, r1"].map(m => expectedAt("vappend", solution, m)),
    ["r : Nat()", "p : Plus(Succ(m1), n, Succ(r1))", "u : Vec(A, Succ(r1))"]);
});

test("vappend: the run knows the length is three, the checker knows only r, so vhead rejects u", () => {
  const { solution } = page("vappend");
  const { r, info } = infoAt("vappend", solution, "print u");
  assert.deepEqual(verdicts(r), [false, true, true]);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Succ(Succ(Zero())))", "VCons(Nat(), Succ(Succ(Zero())), Zero(), " +
    "VCons(Nat(), Succ(Zero()), Succ(Zero()), VCons(Nat(), Zero(), Succ(Succ(Zero())), VNil(Nat()))))"]);
  for (const e of ["r : Nat()", "p : Plus(Succ(Succ(Zero())), Succ(Zero()), r)", "u : Vec(Nat(), r)"])
    assert.ok(scopeOf(info).includes(e), e);
  assert.match(run("vappend", `${solution}print vhead(Nat(), two, u);\n`).r.error?.message() ?? "",
    /must have type `Vec\(Nat\(\), Succ\(Succ\(Succ\(Zero\(\)\)\)\)\)`, and this has type `Vec\(Nat\(\), r\)`/);
});

test("plus-zero: a type contains no function call", () => {
  const learner = "fn bad(n : Nat()) -> (e : Eq(Nat(), plus(n, Zero()), n)) {\n  sorry(_)\n}\n";
  assert.match(run("plus-zero", learner).r.error?.message() ?? "", /a type contains no function call/);
});

test("sorry: sorry(_) takes the let's type, taints p, and an explicit telescope works at an argument", () => {
  const { initial } = page("sorry");
  const { r } = run("sorry", initial);
  assert.deepEqual(verdicts(r), [true, true, false]);
  assert.deepEqual(r.prints.map(p => p.value), ["sorry"]);
  assert.equal(expectedAt("sorry", initial, "sorry(_)"), "p : Even(Succ(Succ(Succ(Succ(Zero())))))");
  const { source } = run("sorry", initial);
  const hole = source.lastIndexOf("sorry(_)") + 6;
  assert.deepEqual([standsFor(r, hole), r.explainAt(hole)?.span], [["p : Even(Succ(Succ(Succ(Succ(Zero())))))"], { start: hole, end: hole + 1 }]);
  assert.deepEqual(infoAt("sorry", initial, "print").info.scope.find(e => e.names.includes("p"))?.tainted, ["p"]);
  const step = initial.replace("sorry(_);", "EvenSucc(three, sorry(q : Odd(three)));");
  assert.equal(run("sorry", step).r.error, null);
  assert.equal(expectedAt("sorry", step, "sorry(q"), "p : Odd(Succ(Succ(Succ(Zero()))))");
});

test("equality: two in the goal canonicalizes to Succ(Succ(Zero())) in two rewrites", () => {
  const p = page("equality");
  const source = program(p.boxes, p.initial);
  const explained = explainTerm(check(source, p.phase), source.indexOf("two, Succ(Succ"));
  assert.equal(explained?.canonical.text, "Succ(Succ(Zero()))");
  assert.equal(explained?.rewrites.length, 2);
});

test("soundness: marking n subterm does not help loop, a match with no branches is rejected, and sorry leaves the goal unproved", () => {
  assert.match(run("soundness", page("soundness").initial.replace("loop(n)", "match n : _ {}")).r.error?.message() ?? "", /no branch for `Zero`, `Succ`/);
  const marked = page("soundness").initial.replace("loop(n : Nat())", "loop(subterm n : Nat())").replace("loop(n)", "loop(subterm n)");
  assert.match(run("soundness", marked).r.error?.message() ?? "", /not a strict subterm/);
  assert.deepEqual(verdicts(run("soundness", page("soundness").solution).r), [true, true, false]);
});

test("times-distrib: a binder the later clauses of its `let` refer to needs a type", () => {
  const p = page("times-distrib");
  const r = check(program(p.boxes.map(b => b.replace("let (yxz : Nat(),", "let (yxz,")), p.solution), p.phase);
  assert.match(r.error?.message() ?? "", /`yxz` has no type here/);
});

test("comptime: n is known only by its type, so only the run proves Even(n)", () => {
  const { r } = run("comptime", page("comptime").solution);
  assert.deepEqual(verdicts(r), [false, true, true]);
  assert.equal(r.prints[0]?.value, `${"Succ(".repeat(100)}Zero()${")".repeat(100)}`);
  assert.match(run("comptime", page("comptime").initial).r.error?.message() ?? "", /`None` is not refuted/);
  assert.match(run("comptime", "qed EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()));\n").r.error?.message() ?? "", /type `Even\(n\)`/);
  const fallback = run("comptime", "let p = match decideEven(n) : (p : Even(n)) {\n  None(_) => sorry(_);\n  Some(_, q) => q;\n};\nqed p;\n").r;
  assert.deepEqual(verdicts(fallback), [true, true, false]);
});

test("iszero: the Succ branch cannot be filled with Refl, and the match on p takes its annotation from the branch", () => {
  const { source, r } = run("iszero", page("iszero").solution);
  assert.deepEqual(standsFor(r, source.indexOf("p : _") + 4), ["e : Eq(Nat(), Succ(m), Zero())"]);
  const junk = page("iszero").solution.replace("match p : _ {}", "Refl(Nat(), n)");
  assert.match(run("iszero", junk).r.error?.message() ?? "", /Eq\(Nat\(\), Succ\(m\), Zero\(\)\)/);
});
