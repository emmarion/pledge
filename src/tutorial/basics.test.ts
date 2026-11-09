import { test } from "node:test";
import assert from "node:assert/strict";
import { scopeOf } from "../../tests/helpers.ts";
import { page, run } from "../../tests/tutorial.ts";
import type { PositionInfo } from "../api.ts";

const errorAt = (slug: string, learner: string) => {
  const { source, r } = run(slug, learner);
  return { at: r.error ? source.slice(r.error.span.start, r.error.span.end) : null, message: r.error?.message() ?? "" };
};
const expected = (info: PositionInfo) => info.expected.entries?.map(e => `${e.name} : ${e.type?.text}${e.rule ? ` is ${e.rule.text}` : ""}`);
const printsOf = (slug: string) => run(slug, page(slug).solution).r.prints.map(p => p.value);

test("nat: the solution prints two and three", () => {
  assert.deepEqual(printsOf("nat"), ["Succ(Succ(Zero()))", "Succ(Succ(Succ(Zero())))"]);
});

test("functions: the starting text fails at the match for want of a Succ branch, and Expected there is b : Bool()", () => {
  const { source, r } = run("functions", page("functions").initial);
  assert.equal(r.error?.span.start, source.indexOf("match n"));
  assert.match(r.error?.message() ?? "", /no branch for `Succ`/);
  assert.deepEqual(expected(r.infoAt(source.indexOf("match n"))), ["b : Bool()"]);
  assert.deepEqual(printsOf("functions"), ["False()"]);
  assert.match(errorAt("functions", page("functions").solution.replace("Succ(_)", "Succ(Succ(m))")).message, /a pattern does not nest/);
});

test("knowledge: Scope shows two's rule canonically, and the Term panel and the At the caret field show the rewrites", () => {
  const { source, r } = run("knowledge", page("knowledge").initial);
  const at = source.lastIndexOf("two");
  assert.ok(scopeOf(r.infoAt(at)).includes("two : Nat() is Succ(Succ(Zero()))"));
  const explained = r.explainAt(at);
  assert.equal(explained?.canonical.text, "Succ(Succ(Zero()))");
  assert.deepEqual(explained?.rewrites.map(w => `${w.from.text} -> ${w.to.text}`), ["two -> Succ(one)", "Succ(one) -> Succ(Succ(Zero()))"]);
  const typed = r.evalAt(at, "Succ(two)");
  assert.ok(!("error" in typed));
  assert.deepEqual([typed.type.text, typed.rule?.text, typed.canonicalRule?.text], ["Nat()", "Succ(two)", "Succ(Succ(Succ(Zero())))"]);
  assert.equal(r.error?.span.start, at);
  assert.match(r.error?.message() ?? "", /`Succ\(Zero\(\)\)`, and this is `Succ\(Succ\(Zero\(\)\)\)`/);
  assert.equal(r.inspects.length, 1);
});

test("vhead: VNil is refuted at the match, a branch for it is an error, and an empty vector is rejected", () => {
  const { source, r } = run("vhead", page("vhead").solution);
  assert.deepEqual(r.infoAt(source.indexOf("match v")).refutations?.map(x => x.ctor), ["VNil"]);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())"]);
  assert.match(errorAt("vhead", page("vhead").solution.replace("    VCons", "    VNil(_) => v;\n    VCons")).message, /`VNil` is refuted/);
  assert.equal(errorAt("vhead", `${page("vhead").solution}print vhead(Nat(), Zero(), VNil(Nat()));\n`).at, "VNil(Nat())");
});

test("vuncons: Expected on the branch body lists both returns, then one per tuple element", () => {
  const initial = run("vuncons", page("vuncons").initial);
  const body = initial.source.indexOf("=> h") + 3;
  assert.equal(initial.r.error?.span.start, body);
  assert.match(initial.r.error?.message() ?? "", /2 values are expected here, and this produces 1/);
  assert.deepEqual(expected(initial.r.infoAt(body)), ["hd : A", "tl : Vec(A, n)"]);
  const { source, r } = run("vuncons", page("vuncons").solution);
  const tuple = source.indexOf("(h, t);");
  assert.deepEqual([expected(r.infoAt(tuple + 1)), expected(r.infoAt(tuple + 4))], [["hd : A"], ["tl : Vec(A, n)"]]);
  const half = errorAt("vuncons", page("vuncons").initial.replace("=> h;", "=> (h, t);"));
  assert.equal(half.at, "vuncons(Nat(), one, xs)");
  assert.match(half.message, /1 value is expected here, and this produces 2/);
});

test("is-binders: without the promise m is only a number; with it, m is Succ(Zero()) and a false promise is rejected", () => {
  const before = run("is-binders", page("is-binders").initial);
  const last = before.source.indexOf("print vhead");
  assert.deepEqual(scopeOf(before.r.infoAt(last)), ["m : Nat()", "w : Vec(Nat(), m)"]);
  assert.equal(before.r.error?.span.start, before.source.indexOf("w);"));
  const after = run("is-binders", page("is-binders").solution);
  assert.deepEqual(scopeOf(after.r.infoAt(after.source.indexOf("print vhead"))), ["m : Nat() is Succ(Zero())", "w : Vec(Nat(), Succ(Zero()))"]);
  assert.deepEqual(after.r.prints.map(p => p.value), ["Zero()"]);
  assert.equal(errorAt("is-binders", page("is-binders").solution.replace("m is Succ(n)", "m is Succ(Succ(n))")).at, "Succ(n)");
});

test("pattern-let: VNil is refuted at the let, rest is one shorter, and let Succ(k) = n is rejected", () => {
  const { source, r } = run("pattern-let", page("pattern-let").initial);
  assert.deepEqual(r.infoAt(source.indexOf("let VCons")).refutations?.map(x => x.ctor), ["VNil"]);
  assert.ok(scopeOf(r.infoAt(source.indexOf("rest\n}"))).includes("rest : Vec(A, Succ(n))"));
  assert.equal(r.error?.span.start, source.indexOf("rest\n}"));
  assert.deepEqual(printsOf("pattern-let"), ["Succ(Zero())"]);
  const succ = errorAt("pattern-let", page("pattern-let").solution.replace("  let VCons(_, _, _", "  let Succ(k) = n;\n  let VCons(_, _, _"));
  assert.equal(succ.at, "Succ(k)");
  assert.match(succ.message, /`Zero` is not refuted/);
});

test("termination: the unmarked call is an error about plus's group, m is Succ(k) there, and the solution prints six", () => {
  const { source, r } = run("termination", page("termination").initial);
  const call = source.indexOf("plus(k, n)");
  assert.equal(r.error?.span.start, call);
  assert.match(r.error?.message() ?? "", /`plus`'s group/);
  const info = r.infoAt(call);
  assert.ok(scopeOf(info).includes("m : Nat() is Succ(k)"));
  assert.deepEqual(info.termination, { fn: "plus", subtermParams: [], group: ["plus"] });
  assert.deepEqual(printsOf("termination"), [`${"Succ(".repeat(6)}Zero()${")".repeat(6)}`]);
});

test("mutual: isOdd's group is isEven and isOdd, and EvenZero() is not evidence that two is even", () => {
  const { source, r } = run("mutual", page("mutual").initial);
  assert.deepEqual(r.infoAt(source.indexOf("=> False()")).termination?.group, ["isEven", "isOdd"]);
  const half = errorAt("mutual", page("mutual").initial.replace("False();", "False();\n      Succ(m) => isEven(subterm m);"));
  assert.equal(half.at, "EvenZero()");
  assert.match(half.message, /`Even\(Zero\(\)\)`/);
});
