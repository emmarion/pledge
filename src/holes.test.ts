import { test } from "node:test";
import assert from "node:assert/strict";
import type { CheckResult } from "./api.ts";
import { harness, nat, vecBy, verdicts } from "../tests/helpers.ts";

const one = harness(1), two = harness(2);
const vec = vecBy(""), erasedVec = vecBy("erased ");
const eq = "data Eq(A : Type(), a : A, b : A) : Type() {\n  Refl(A : Type(), a : A) : Eq(A, a, a);\n}\n";
const box = "data Box(A : Type()) : Type() {\n  MkBox(A : Type(), x : A) : Box(A);\n}\n";
const wrap = "data Head(n : Nat()) : Type() {\n  HeadSucc(erased m : Nat()) : Head(Succ(m));\n}\ndata Wrap(n : Nat()) : Type() {\n  W(erased n : Nat(), h : Head(n)) : Wrap(n);\n}\n";
const prints = (r: CheckResult): string[] => r.prints.map(p => p.value);
const noneOfThese = /`_` stands for an argument that is erased or has type `Type\(\)`, or for part of a type/;
const unsolved = /cannot be inferred/;

test("phase 1: _ stands for an argument of type Type(), and print shows it as _", () => {
  assert.deepEqual(prints(one.ok(`${nat}${vec}print VCons(_, Zero(), Zero(), VNil(_));\n`)), ["VCons(_, Zero(), Zero(), VNil(_))"]);
  const mk = `${nat}${vec}fn mk(A : Type(), x : A) -> (r : Vec(A, Succ(Zero()))) {\n  VCons(_, Zero(), x, VNil(_))\n}\nprint mk(_, Zero());\n`;
  assert.deepEqual(prints(one.ok(mk)), ["VCons(_, Zero(), Zero(), VNil(_))"]);
  one.err(`${nat}${vec}print VCons(Nat(), _, Zero(), VNil(Nat()));\n`, "_", noneOfThese);
  one.err(`${nat}print Succ(_);\n`, "_", noneOfThese);
  one.err(`${nat}${vec}print VNil(_);\n`, "_", unsolved);
});

test("phase 1: _ inside a type, at any depth and as a whole type", () => {
  assert.deepEqual(prints(one.ok(`${nat}${eq}print Eq(_, Zero(), Zero());\n`)), ["_"]);
  assert.deepEqual(prints(one.ok(`${nat}${vec}let v : Vec(_, _) = VCons(Nat(), Zero(), Zero(), VNil(Nat()));\nlet w : Vec(Nat(), _) = VNil(_);\nlet z : _ = Zero();\nprint w;\n`)), ["VNil(_)"]);
  one.ok(`${nat}${eq}fn f(n : Nat(), p : Eq(_, n, n)) -> (q : Eq(_, n, n)) {\n  p\n}\n`);
  one.ok(`${nat}${vec}let (m : Nat(), v : Vec(_, m)) = (Zero(), VNil(Nat()));\nlet w is VNil(_) = v;\n`);
  assert.deepEqual(verdicts(one.ok(`${nat}${eq}goal Eq(_, Zero(), Zero());\nqed Refl(_, Zero());\n`)), [false, true, true]);
  one.err(`${nat}${vec}fn f(n : Nat(), v : Vec(_, n)) -> (r : Nat()) {\n  n\n}\n`, "_", unsolved);
  one.err(`${nat}${vec}print Vec(Nat(), Succ(_));\n`, "_", unsolved);
  one.err(`${nat}fn f(n : _) -> (r : Nat()) {\n  Zero()\n}\n`, "_", unsolved);
  one.err(`${nat}let x is _ = Zero();\n`, "_", /stands only for a whole argument or inside a type/);
  one.err(`${nat}${vec}let v : Vec(_, Succ(_)) = VNil(Nat());\n`, "VNil(Nat())", /binder `v` must have type `Vec\(Nat\(\), Succ\(_@\d+:\d+\)\)`/);
  assert.deepEqual(prints(one.ok(`${nat}${vec}let (v : Vec(_, Zero()), w : Vec(Nat(), Zero()), e is v) = (VNil(Nat()), VNil(Nat()), VNil(Nat()));\nprint e;\n`)), ["VNil(_)"]);
  const pair = `${nat}${vec}fn pair() -> (m : Nat(), v : Vec(Nat(), m)) {\n  (Zero(), VNil(_))\n}\n`;
  assert.deepEqual(prints(one.ok(`${pair}let (m : Nat(), v : Vec(Nat(), _)) = pair();\nlet (k, u : Vec(_, _)) = pair();\nprint u;\n`)), ["VNil(_)"]);
  one.err(`${nat}${vec}let y : Vec(_, _) = sorry(_);\n`, "_", /none is given here/, "sorry(");
});

test("an evaluated _ shows as _, whatever it is solved to, and nothing inside a type runs", () => {
  const anon = `${nat}${vec}fn pair() -> (T : Type(), x : T) {\n  (Nat(), Zero())\n}\nlet (_, x) = pair();\nprint VCons(_, Zero(), x, VNil(_));\n`;
  assert.deepEqual(prints(one.ok(anon)), ["VCons(_, Zero(), Zero(), VNil(_))"]);
  assert.deepEqual(prints(two.ok(`${nat}${box}fn h(erased A : Type(), x : A) -> (b : Box(A)) {\n  MkBox(_, x)\n}\nprint h(Nat(), Zero());\n`)), ["MkBox(_, Zero())"]);
  const pred = `${nat}${vec}data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\nfn keep(n : Nat(), p : IsZero(n)) -> (r : Nat()) {\n  match n : _ {\n    Zero() => n;\n    Succ(m) => m;\n  }\n}\n`;
  assert.deepEqual(prints(one.ok(`${pred}print Vec(Nat(), keep(Zero(), IsZeroHere()));\nprint Vec(Nat(), Succ(Zero()));\n`)), ["_", "_"]);
  assert.deepEqual(prints(one.ok(`${pred}print Vec(Nat(), keep(_, IsZeroHere()));\n`)), ["_"]);
  one.err(`${pred}print keep(_, IsZeroHere());\n`, "_", noneOfThese, "keep(_");
});

test("a call closes its _, and an application of a value constructor leaves its _ to what surrounds it", () => {
  const mk = `${nat}${erasedVec}fn mk(erased B : Type()) -> (v : Vec(B, Zero())) {\n  VNil(_)\n}\n`;
  two.ok(`${mk}let x : Vec(Nat(), Zero()) = mk(_);\nlet y : Vec(Nat(), _) = VNil(_);\nlet z : Vec(Nat(), _) = mk(_);\n`);
  two.err(`${mk}let x = mk(_);\n`, "_", unsolved, "mk(_);");
  two.ok(`${nat}${wrap}fn f(n : Nat()) -> (w : Wrap(Succ(n))) {\n  W(_, HeadSucc(_))\n}\n`);
  const app = `${nat}${erasedVec}fn second(erased A : Type(), erased n : Nat(), v : Vec(A, Zero()), w : Vec(A, n)) -> (r : Vec(A, n)) {\n  w\n}\n`;
  assert.deepEqual(prints(two.ok(`${app}print second(_, _, VNil(_), VCons(_, _, Zero(), VNil(_)));\n`)), ["VCons(_, _, Zero(), VNil(_))"]);
  two.err(`${app}fn len(erased A : Type(), v : Vec(A, Zero())) -> (r : Nat()) {\n  Zero()\n}\nprint len(_, VNil(_));\n`, "_", unsolved, "len(_, VNil");
});

test("a branch body and a scrutinee close their _", () => {
  const pick = `${nat}${box}fn pick(n : Nat()) -> (b : Box(Nat())) {\n  match n : _ {\n    Zero() => MkBox(_, n);\n    Succ(m) => MkBox(_, m);\n  }\n}\nprint pick(Zero());\n`;
  assert.deepEqual(prints(two.ok(pick)), ["MkBox(_, Zero())"]);
  two.err(`${nat}${erasedVec}fn f(n : Nat()) -> (r : Nat()) {\n  match VNil(_) : _ {\n    VNil(_) => n;\n  }\n}\n`, "_", unsolved, "match VNil(");
});

test("taint: a _ solved to a tainted term taints the results built from it, and no others", () => {
  const source = `${nat}${box}let t = sorry(T : Type());\nprint MkBox(_, sorry(x : t));\nlet (z : Box(_), k) = (MkBox(_, sorry(x : t)), Zero());\nprint k;\nprint z;\n`;
  assert.deepEqual(prints(two.ok(source)), ["sorry", "Zero()", "sorry"]);
});

test("taint: a _ already solved to a tainted term when its application is built taints the result (§12)", () => {
  const w = "data False() : Type() {}\nlet erased s = sorry(p : False());\ndata W() : Type() {\n  MkW(erased p is s) : W();\n}\n";
  const f = (arg: string) => `${w}fn f() -> (r : False()) {\n  let erased MkW(q) = MkW(${arg});\n  match erased q : _ {}\n}\n`;
  for (const arg of ["_", "s"]) {
    assert.deepEqual(verdicts(two.ok(`${f(arg)}goal fn () -> (r : False());\nqed f;\n`)), [true, true, false], arg);
    assert.deepEqual(prints(two.ok(`${f(arg)}print f();\n`)), ["sorry"], arg);
  }
  const pack = (arg: string) => `${nat}let t = sorry(T : Type());\ndata K(A : Type()) : Type() {\n  MkK() : K(t);\n}\ndata Pack() : Type() {\n  MkPack(A : Type(), k : K(A)) : Pack();\n}\nlet p = MkPack(${arg}, MkK());\nprint p;\ngoal Pack();\nqed p;\n`;
  for (const arg of ["_", "t"]) {
    const r = one.ok(pack(arg));
    assert.deepEqual([prints(r), verdicts(r)], [["sorry"], [true, true, false]], arg);
  }
  const is = `${w}data Is(x : W()) : Type() {\n  MkIs(x : W()) : Is(x);\n}\ngoal Is(MkW(_));\nqed MkIs(MkW(_));\n`;
  assert.deepEqual(verdicts(two.ok(is)), [true, true, false]);
});

test("explainAt works at a _ in a let binder solved to what the right-hand side produces", () => {
  const source = `${nat}${vec}fn pair() -> (m : Nat(), v : Vec(Nat(), m)) {\n  (Zero(), VNil(Nat()))\n}\nlet (k, u : Vec(_, _)) = pair();\n`;
  const r = one.ok(source);
  for (let at = source.indexOf("let (k"); at < source.length; at++) r.explainAt(at);
});
