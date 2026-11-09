import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { verdicts } from "../../tests/helpers.ts";
import { page, program, run } from "../../tests/tutorial.ts";

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

test("iszero: the Succ branch cannot be filled with Refl", () => {
  const junk = page("iszero").solution.replace("match p : _ {}", "Refl(Nat(), n)");
  assert.match(run("iszero", junk).r.error?.message() ?? "", /Eq\(Nat\(\), Succ\(m\), Zero\(\)\)/);
});
