import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { entriesOf, explainTerm, listed, namedOf, standsFor, verdicts } from "../../tests/helpers.ts";
import { errorAt, expected, expectedAt, infoAt, page, program, run } from "../../tests/tutorial.ts";

test("evidence: only real evidence that two is even proves the goal", () => {
  const { initial, solution } = page("evidence");
  assert.deepEqual(verdicts(run("evidence", initial).r), [false, null, false]);
  assert.deepEqual(verdicts(run("evidence", solution).r), [false, true, true]);
  const wrong = errorAt("evidence", "qed EvenZero();\n");
  assert.equal(wrong.at, "EvenZero()");
  assert.match(wrong.message, /`Even\(Zero\(\)\)`/);
  assert.match(errorAt("evidence", "qed OddSucc(Zero(), EvenZero());\n").message, /`Odd\(Succ\(Zero\(\)\)\)`/);
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
  assert.deepEqual(listed(infoAt("sorry", initial, "print").info).find(e => e.names.includes("p"))?.tainted, ["p"]);
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

test("eq-use: a Refl is rejected until e is matched; in the Refl branch b is a, and a pattern let does the same", () => {
  const { initial, solution } = page("eq-use");
  const start = infoAt("eq-use", initial, "sorry(_)");
  assert.deepEqual(verdicts(start.r), [true, null, null]);
  assert.deepEqual([expected(start.info), namedOf(start.info)],
    [["f : Eq(Nat(), Succ(a), Succ(b))"], ["a : Nat()", "b : Nat()", "e : Eq(Nat(), a, b)"]]);
  assert.match(errorAt("eq-use", initial.replace("  sorry(_)", "  Refl(Nat(), Succ(a))")).message,
    /must have type `Eq\(Nat\(\), Succ\(a\), Succ\(b\)\)`, and this has type `Eq\(Nat\(\), Succ\(a\), Succ\(a\)\)`/);
  const half = infoAt("eq-use", solution.replace("=> Refl(Nat(), Succ(a))", "=> sorry(_)"), "sorry(_)");
  assert.deepEqual(expected(half.info), ["f : Eq(Nat(), Succ(a), Succ(a))"]);
  assert.ok(entriesOf(half.info).includes("b : Nat() is a"));
  assert.deepEqual(verdicts(run("eq-use", solution).r), [false, null, null]);
  assert.equal(run("eq-use", initial.replace("  sorry(_)", "  let Refl(_, _) = e;\n  Refl(Nat(), Succ(a))")).r.error, null);
});

test("iszero: the Succ branch cannot be filled with Refl, and the match on p takes its annotation from the branch", () => {
  const { source, r } = run("iszero", page("iszero").solution);
  assert.deepEqual(standsFor(r, source.indexOf("p : _") + 4), ["e : Eq(Nat(), Succ(m), Zero())"]);
  const junk = page("iszero").solution.replace("match p : _ {}", "Refl(Nat(), n)");
  assert.match(run("iszero", junk).r.error?.message() ?? "", /Eq\(Nat\(\), Succ\(m\), Zero\(\)\)/);
});
