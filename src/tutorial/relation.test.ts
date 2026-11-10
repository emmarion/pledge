import { test } from "node:test";
import assert from "node:assert/strict";
import { scopeOf, verdicts } from "../../tests/helpers.ts";
import { expectedAt, gapsTest, infoAt, page, run } from "../../tests/tutorial.ts";

test("plus-relation: the evidence is built a layer at a time, and the checker knows the call's result only through Plus", () => {
  const { initial, solution } = page("plus-relation");
  const start = run("plus-relation", initial).r;
  assert.deepEqual(verdicts(start), [true, true, false]);
  assert.equal(expectedAt("plus-relation", initial, "sorry(_)"), "e : Plus(Succ(Succ(Zero())), Succ(Succ(Zero())), Succ(Succ(Succ(Succ(Zero())))))");
  const layer = initial.replace("= sorry(_)", "= PlusSucc(one, two, three, sorry(p : Plus(one, two, three)))");
  assert.equal(run("plus-relation", layer).r.error, null);
  assert.equal(expectedAt("plus-relation", layer, "sorry(p"), "p : Plus(Succ(Zero()), Succ(Succ(Zero())), Succ(Succ(Succ(Zero()))))");
  const { r, info } = infoAt("plus-relation", solution, "print q");
  assert.deepEqual(verdicts(r), [false, true, true]);
  assert.equal(r.prints[0]?.value, "Succ(Succ(Succ(Succ(Zero()))))");
  assert.equal(r.prints[1]?.value, info.scope.find(e => e.names.includes("e"))?.rule?.text);
  for (const e of ["s : Nat()", "q : Plus(Succ(Succ(Zero())), Succ(Succ(Zero())), s)"]) assert.ok(scopeOf(info).includes(e), e);
});

test("plus-relation: a type contains no function call", () => {
  const learner = "fn bad(n : Nat()) -> (e : Eq(Nat(), plus(n, Zero()), n)) {\n  sorry(_)\n}\n";
  assert.match(run("plus-relation", learner).r.error?.message() ?? "", /a type contains no function call/);
});


gapsTest([
  ["plus-zero", ["e : Eq(Nat(), Zero(), Zero())", "e : Eq(Nat(), Succ(r1), Succ(m))"], null],
  ["vappend", ["r : Nat(), p : Plus(Zero(), n, r), u : Vec(A, r)", "r : Nat(), p : Plus(Succ(m1), n, r), u : Vec(A, r)"]],
]);

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
