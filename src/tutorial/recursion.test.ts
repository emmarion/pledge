import { test } from "node:test";
import assert from "node:assert/strict";
import { scopeOf } from "../../tests/helpers.ts";
import { errorAt, expected, page, printsOf, run } from "../../tests/tutorial.ts";

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

test("mutual: isOdd's group is isEven and isOdd, outside a block isEven cannot call isOdd, and the run answers", () => {
  const { initial, solution } = page("mutual");
  const { source, r } = run("mutual", initial);
  assert.deepEqual(r.infoAt(source.indexOf("=> No()")).termination?.group, ["isEven", "isOdd"]);
  assert.match(r.error?.message() ?? "", /no branch for `Succ`/);
  assert.deepEqual(printsOf("mutual"), ["Yes()", "No()"]);
  const apart = errorAt("mutual", solution.replace("mutual {\n", "").replace("  }\n}\nlet", "  }\nlet"));
  assert.equal(apart.at, "isOdd");
  assert.match(apart.message, /not in scope/);
});

test("vzip: each branch knows n, so w is taken apart with VNil refuted; the start fails at ws, and unequal lengths are rejected", () => {
  const { initial, solution } = page("vzip");
  const { source, r } = run("vzip", initial);
  const nil = r.infoAt(source.indexOf("VNil(Pair"));
  assert.deepEqual(expected(nil), ["r : Vec(Pair(A, B), Zero())"]);
  assert.ok(scopeOf(nil).includes("n : Nat() is Zero()") && scopeOf(nil).includes("w : Vec(B, Zero())"));
  const cons = r.infoAt(source.indexOf("let VCons"));
  for (const e of ["n : Nat() is Succ(k)", "v : Vec(A, Succ(k)) is VCons(A, k, x, vs)", "w : Vec(B, Succ(k))"]) assert.ok(scopeOf(cons).includes(e), e);
  assert.deepEqual(cons.refutations?.map(x => x.ctor), ["VNil"]);
  assert.deepEqual(errorAt("vzip", initial), { at: "ws", message: "field `rest` of `VCons` must have type `Vec(Pair(A, B), k)`, and this has type `Vec(B, k)`" });
  assert.match(errorAt("vzip", solution.replace("subterm vs", "vs")).message, /`vzip`'s group/);
  assert.deepEqual(printsOf("vzip"), ["VCons(_, Succ(Zero()), MkPair(_, _, Zero(), Zero()), " +
    "VCons(_, Zero(), MkPair(_, _, Succ(Zero()), Succ(Zero())), VNil(_)))"]);
  const unequal = errorAt("vzip", `${solution}print vzip(Nat(), Nat(), Succ(one), xs, VNil(Nat()));\n`);
  assert.equal(unequal.at, "VNil(Nat())");
  assert.match(unequal.message, /parameter `w` of `vzip` must have type `Vec\(Nat\(\), Succ\(Succ\(Zero\(\)\)\)\)`/);
});
