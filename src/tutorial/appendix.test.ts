import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { scopeOf, verdicts } from "../../tests/helpers.ts";
import { page, program, run } from "../../tests/tutorial.ts";

test("tuple-let-telescope: Expected lists both binders, and dropping m's type is an error at the reference", () => {
  const { source, r } = run("tuple-let-telescope", page("tuple-let-telescope").solution);
  assert.deepEqual(r.infoAt(source.indexOf("pair(x)")).expected.entries?.map(e => `${e.name} : ${e.type?.text}`), ["m : Nat()", "v : Vec(Nat(), Succ(m))"]);
  assert.ok(scopeOf(r.infoAt(source.indexOf("print v"))).includes("v : Vec(Nat(), Succ(m))"));
  const dropped = run("tuple-let-telescope", page("tuple-let-telescope").solution.replace("m : Nat(),", "m,"));
  assert.match(dropped.r.error?.message() ?? "", /`m` has no type here/);
  assert.equal(dropped.r.error?.span.start, dropped.source.indexOf("Succ(m)))") + 5);
});

test("facts-escape: after the block, v's rule and the anonymous tail remain, and the goal needs them", () => {
  const { source, r } = run("facts-escape", page("facts-escape").solution);
  const after = scopeOf(r.infoAt(source.indexOf("inspect;")));
  assert.ok(after.some(e => /^v : .* is VCons\(Nat\(\), n, h, \?VCons\.rest@/.test(e)), after.join("; "));
  assert.ok(after.includes("?VCons.rest : Vec(Nat(), n)"), after.join("; "));
  const tail = r.infoAt(source.indexOf("inspect;")).scope.find(e => e.origin.kind === "VCons.rest")!;
  assert.equal(source.slice(tail.origin.span.start, tail.origin.span.end), "tl");  assert.ok(!after.some(e => /^(hd|tl)\b/.test(e)));
  assert.match(run("facts-escape", `let k = tl;\n${page("facts-escape").solution}`).r.error?.message() ?? "", /`tl` is not in scope/);
  const p = page("facts-escape");
  const noEscape = check(program(p.boxes.map(b => b.replace("{ let VCons(_, _, hd, tl) = v; hd }", "Zero()")), p.solution), p.phase);
  assert.equal(noEscape.goalProved, false);
});

test("tainted-pattern-let: every statement checks, yet print shows sorry and the goal is not proved; in a branch only the match is tainted", () => {
  const { r } = run("tainted-pattern-let", page("tainted-pattern-let").initial);
  assert.equal(r.error, null);
  assert.deepEqual(verdicts(r), [true, true, false]);
  assert.deepEqual(r.prints.map(p => p.value), ["sorry", "Zero()", "sorry"]);
  assert.deepEqual(run("tainted-pattern-let", page("tainted-pattern-let").solution).r.prints.map(p => p.value), ["sorry", "Zero()", "Zero()"]);
});

test("hole-through-block: the _s are solved through the block's final expression", () => {
  const { source, r } = run("hole-through-block", page("hole-through-block").solution);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())", "Succ(Zero())"]);
  const at = source.indexOf("vhead(_, _, { let") + 6;
  assert.deepEqual([r.explainAt(at)?.canonical.text, r.explainAt(at + 3)?.canonical.text], ["Nat()", "Zero()"]);
  assert.deepEqual(r.infoAt(at).expected.entries?.map(e => [e.name, e.erased]), [["A", true]]);
});

test("hole-taint: a _ solved to a sorry result taints the call; with Nat() the goal is proved", () => {
  const { source, r } = run("hole-taint", page("hole-taint").initial);
  assert.deepEqual([verdicts(r), r.prints.map(p => p.value)], [[true, true, false], ["sorry"]]);
  assert.equal(r.explainAt(source.indexOf("VNil(_));") + 5)?.canonical.text, "A");
  const clean = run("hole-taint", page("hole-taint").solution).r;
  assert.deepEqual([verdicts(clean), clean.prints.map(p => p.value)], [[false, true, true], ["Zero()"]]);
});

test("goal-comparison: an earlier is clause is not in force, so the starting text names return 1; changing the goal also works", () => {
  const { r } = run("goal-comparison", page("goal-comparison").initial);
  assert.match(r.error?.message() ?? "", /`succEq`'s return 1 is `e : Eq\(Nat\(\), Succ\(a\), b\)`, and the goal's is `e : Eq\(Nat\(\), b, Succ\(a\)\)`/);
  assert.deepEqual(verdicts(r), [false, false, false]);
  const goalChanged = run("goal-comparison", page("goal-comparison").initial.replace("Eq(Nat(), b, Succ(a))", "Eq(Nat(), Succ(a), b)")).r;
  assert.deepEqual(verdicts(goalChanged), [false, true, true]);
});

test("absurd-branches: Succ is absurd, IsZeroHere refuted, and print runs the live branch", () => {
  const { source, r } = run("absurd-branches", page("absurd-branches").solution);
  assert.deepEqual(r.prints.map(p => p.value), ["Zero()"]);
  assert.deepEqual(r.infoAt(source.indexOf("match erased") + 2).refutations?.map(x => [x.ctor, x.kind]), [["Succ", "absurd"]]);
  assert.deepEqual(r.infoAt(source.indexOf("match p") + 2).refutations?.map(x => [x.ctor, x.kind]), [["IsZeroHere", "refuted"]]);
  assert.match(run("absurd-branches", page("absurd-branches").initial).r.error?.message() ?? "", /no branch for `Succ`/);
});
