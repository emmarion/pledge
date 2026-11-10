import { test } from "node:test";
import assert from "node:assert/strict";
import { entriesOf, namedOf, standsFor } from "../../tests/helpers.ts";
import { errorAt, expected, page, printsOf, run } from "../../tests/tutorial.ts";

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

test("annotation-underscore: _ in vuncons stands for its returns, and the untyped let is rejected at its _ until y has a type", () => {
  const { initial, solution } = page("annotation-underscore");
  const before = errorAt("annotation-underscore", initial);
  const { source, r } = run("annotation-underscore", initial);
  assert.equal(r.error?.span.start, source.indexOf("t : _") + 4);
  assert.deepEqual(before, { at: "_", message: "`_` stands for the whole telescope given at its position, and none is given here (§10)" });
  assert.deepEqual(expected(r.infoAt(source.indexOf("=> (h, t)") + 3)), ["hd : A", "tl : Vec(A, n)"]);
  const half = run("annotation-underscore", initial.replace("v : (hd : A, tl : Vec(A, n))", "v : _"));
  assert.equal(half.r.error?.span.start, half.source.indexOf("t : _") + 4);
  assert.deepEqual(standsFor(half.r, half.source.indexOf("v : _") + 4), ["hd : A", "tl : Vec(A, n)"]);
  const fixed = run("annotation-underscore", solution);
  const [ann, let_] = ["v : _", "t : _"].map(m => fixed.source.indexOf(m) + 4);
  assert.deepEqual([standsFor(fixed.r, ann!), standsFor(fixed.r, let_!)], [["hd : A", "tl : Vec(A, n)"], ["y : Nat()"]]);
  assert.deepEqual(fixed.r.explainAt(ann!)?.span, { start: ann, end: ann! + 1 });
  assert.deepEqual(printsOf("annotation-underscore"), ["Succ(Zero())"]);
  assert.equal(run("annotation-underscore", initial.replace("let y =", "let y : Nat() =")).r.error, null);
  const block = solution.replace("= match t : _ {", "= { match t : _ {").replace("};\nprint y", "} };\nprint y");
  assert.notEqual(block, solution);
  assert.equal(run("annotation-underscore", block).r.error, null);
  for (const [elsewhere, at] of [["print Succ(match t : _ {\n  VCons(_, _, z, _) => z;\n});\n", "Succ(match t : "],
    ["let (u : Nat(), w : Nat()) = (Zero(), sorry(_));\n", "(Zero(), sorry("]]) {
    const wrong = run("annotation-underscore", `${solution}${elsewhere}`);
    assert.equal(wrong.r.error?.span.start, wrong.source.indexOf(at!) + at!.length);
    assert.equal(wrong.r.error?.message(), before.message);
  }
});

test("is-binders: without the promise m is only a number; with it, m is Succ(Zero()) and a false promise is rejected", () => {
  const before = run("is-binders", page("is-binders").initial);
  const last = before.source.indexOf("print vhead");
  assert.deepEqual(namedOf(before.r.infoAt(last)), ["m : Nat()", "w : Vec(Nat(), m)"]);
  assert.equal(before.r.error?.span.start, before.source.indexOf("w);"));
  const after = run("is-binders", page("is-binders").solution);
  assert.deepEqual(namedOf(after.r.infoAt(after.source.indexOf("print vhead"))), ["m : Nat() is Succ(Zero())", "w : Vec(Nat(), Succ(Zero()))"]);
  assert.deepEqual(after.r.prints.map(p => p.value), ["Zero()"]);
  assert.equal(errorAt("is-binders", page("is-binders").solution.replace("m is Succ(n)", "m is Succ(Succ(n))")).at, "Succ(n)");
});

test("pattern-let: VNil is refuted at the let, rest is one shorter, and let Succ(k) = n is rejected", () => {
  const { source, r } = run("pattern-let", page("pattern-let").initial);
  assert.deepEqual(r.infoAt(source.indexOf("let VCons")).refutations?.map(x => x.ctor), ["VNil"]);
  assert.ok(entriesOf(r.infoAt(source.indexOf("rest\n}"))).includes("rest : Vec(A, Succ(n))"));
  assert.equal(r.error?.span.start, source.indexOf("rest\n}"));
  assert.deepEqual(printsOf("pattern-let"), ["Succ(Zero())"]);
  const succ = errorAt("pattern-let", page("pattern-let").solution.replace("  let VCons(_, _, _", "  let Succ(k) = n;\n  let VCons(_, _, _"));
  assert.equal(succ.at, "Succ(k)");
  assert.match(succ.message, /`Zero` is not refuted/);
});
