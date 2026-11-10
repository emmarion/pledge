import { test } from "node:test";
import assert from "node:assert/strict";
import { explainTerm, scopeOf } from "../../tests/helpers.ts";
import { errorAt, expected, page, printsOf, run } from "../../tests/tutorial.ts";

test("first-look: the first call prints one, the call on the empty vector is rejected at empty, naming both lengths", () => {
  const { source, r } = run("first-look", page("first-look").initial);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())"]);
  assert.equal(r.error?.span.start, source.lastIndexOf("empty"));
  assert.match(r.error?.message() ?? "", /must have type `Vec\(Nat\(\), Succ\(Zero\(\)\)\)`, and this has type `Vec\(Nat\(\), Zero\(\)\)`/);
  assert.deepEqual(printsOf("first-look"), ["Succ(Zero())", "Succ(Zero())"]);
});

test("nat: the solution prints two and three", () => {
  assert.deepEqual(printsOf("nat"), ["Succ(Succ(Zero()))", "Succ(Succ(Succ(Zero())))"]);
});

test("functions: the starting text fails at the match for want of a Succ branch, and Expected there is b : Bool()", () => {
  const { source, r } = run("functions", page("functions").initial);
  assert.equal(r.error?.span.start, source.indexOf("match n"));
  assert.match(r.error?.message() ?? "", /no branch for `Succ`/);
  assert.deepEqual(expected(r.infoAt(source.indexOf("match n"))), ["b : Bool()"]);
  assert.deepEqual(printsOf("functions"), ["No()"]);
  assert.match(errorAt("functions", page("functions").solution.replace("Succ(_)", "Succ(Succ(m))")).message, /a pattern does not nest/);
});

test("knowledge: Scope shows two's rule canonically, and the Term panel and the At the caret field show the rewrites", () => {
  const { source, r } = run("knowledge", page("knowledge").initial);
  const at = source.lastIndexOf("two");
  assert.ok(scopeOf(r.infoAt(at)).includes("two : Nat() is Succ(Succ(Zero()))"));
  const explained = explainTerm(r, at);
  assert.equal(explained?.canonical.text, "Succ(Succ(Zero()))");
  assert.deepEqual(explained?.rewrites.map(w => `${w.from.text} -> ${w.to.text}`), ["two -> Succ(one)", "Succ(one) -> Succ(Succ(Zero()))"]);
  const typed = r.evalAt(at, "Succ(two)");
  assert.ok(!("error" in typed));
  assert.deepEqual([typed.type.text, typed.rule?.text, typed.canonicalRule?.text], ["Nat()", "Succ(two)", "Succ(Succ(Succ(Zero())))"]);
  assert.equal(r.error?.span.start, at);
  assert.match(r.error?.message() ?? "", /`Succ\(Zero\(\)\)`, and this is `Succ\(Succ\(Zero\(\)\)\)`/);
  assert.equal(r.inspects.length, 1);
});
