import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "./check.ts";
import type { CheckResult } from "./api.ts";
import { nat, scopeOf, vecBy } from "../tests/helpers.ts";
import * as examples from "./examples.ts";

const vec = vecBy("");
const front = `${[examples.nat, examples.vec, examples.vheadBy(""), `let x = VCons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), x);`].join("\n\n")}\n`;
const at = (source: string, needle: string, k = 0, from = 0): number => {
  const i = source.indexOf(needle, from);
  assert.ok(i >= 0, `${needle} is not in the source`);
  return i + k;
};
const named = (r: CheckResult, offset: number): string | null => {
  const n = r.nameAt(offset);
  return n === null ? null : n.kind === "entry"
    ? `entry ${n.entry.names.join(",") || `?${n.entry.origin.kind}`} : ${n.entry.type.text}${n.entry.rule ? ` is ${n.entry.rule.text}` : ""}`
    : `${n.kind} ${n.name}${n.signature.text}`;
};

test("a program whose last statement is unfinished keeps what precedes it checked", () => {
  const source = `${nat}let a = Succ(Zero());\nprint a;\nlet b = Succ(`;
  const r = check(source, 1);
  assert.equal(r.error?.span.start, source.length);
  assert.match(r.error?.message() ?? "", /expected an expression/);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())"]);
  const tail = r.infoAt(source.length);
  assert.deepEqual(tail.globals.map(g => g.name), ["Type", "Nat", "a"]);
  assert.deepEqual(tail.globals[1]?.ctors?.map(c => c.name), ["Zero", "Succ"]);
  assert.deepEqual(scopeOf(tail), ["a : Nat() is Succ(Zero())"]);
  assert.equal(named(r, at(source, "print a", 6)), "entry a : Nat() is Succ(Zero())");
  assert.equal(r.nameAt(source.length - 3), null);
  const e = r.evalAt(source.length, "Succ(a)");
  if ("error" in e) assert.fail(e.error.message());
  assert.equal(e.canonicalRule?.text, "Succ(Succ(Zero()))");
  const lexical = check(`${nat}print Zero();\nlet c = Zero(); é`, 1);
  assert.match(lexical.error?.message() ?? "", /non-ASCII/);
  assert.deepEqual([lexical.prints.length, lexical.infoAt(nat.length + 30).scope.map(e => e.names)], [1, [["c"]]]);
});

test("a type error before a syntax error is the one reported", () => {
  const source = `${nat}print Succ(Nat());\nlet b = (;\n`;
  const r = check(source, 1);
  assert.equal(r.error?.span.start, at(source, "Nat());"));
  assert.match(r.error?.message() ?? "", /must have type `Nat\(\)`/);
});

test("the four qed states, and goalProved null only without a goal keyword", () => {
  const states = (source: string) => { const r = check(source, 1); return [r.qed, r.goalProved]; };
  assert.deepEqual(states(`${nat}print Zero();\n`), ["none", null]);
  assert.deepEqual(states(`${nat}goal Nat();\nqed Zero();\n`), ["checks", true]);
  assert.deepEqual(states(`${nat}goal Nat();\nqed Nat();\n`), ["fails", false]);
  assert.deepEqual(states(`${nat}qed Zero();\ngoal Nat();\n`), ["fails", false]);
  assert.deepEqual(states(`${nat}goal Nat();\nqed Zero();\nqed Zero();\n`), ["fails", false]);
  assert.deepEqual(states(`${nat}goal Nat();\nprint Succ(Nat());\nqed Zero();\n`), ["unreached", false]);
  assert.deepEqual(states(`${nat}goal Nat();\nlet b = (;\nqed Zero();\n`), ["unreached", false]);
  assert.deepEqual(states(`${nat}goal Nat();\nqed Zero();\nprint Succ(Nat());\n`), ["checks", false]);
  assert.deepEqual(states(`${nat}goal Nat(\n`), ["none", false]);
});

test("Scope inside a function lists only the function's own entries; at the top level, every named entry", () => {
  const source = `${nat}let a = Zero();\nfn f(n : Nat()) -> (r : Nat()) {\n  let m = Succ(n);\n  inspect;\n  m\n}\nlet b = f(a);\ninspect;\n`;
  const r = check(source, 1);
  assert.deepEqual(r.inspects.map(i => scopeOf(i.info)), [
    ["n : Nat()", "m : Nat() is Succ(n)"],
    ["a : Nat() is Zero()", "b : Nat()"],
  ]);
  assert.deepEqual(scopeOf(r.infoAt(at(source, "n : Nat()"))), []);
  assert.deepEqual(scopeOf(r.infoAt(at(source, "\nlet b"))), ["a : Nat() is Zero()"]);
});

test("an anonymous entry is listed only when something listed mentions it", () => {
  const source = `${nat}${vec}fn f(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (r : A) {\n  let VCons(_, _, h, _) = v;\n  inspect;\n  h\n}\nprint f(Nat(), Zero(), VCons(Nat(), Zero(), Zero(), VNil(Nat())));\ninspect;\n`;
  const [body, after] = check(source, 1).inspects.map(i => scopeOf(i.info));
  assert.deepEqual(body, ["A : Type()", "n : Nat()", "v : Vec(A, Succ(n)) is VCons(A, n, h, _@11:22)", "h : A", "_@11:22 : Vec(A, n)"]);
  assert.deepEqual(after, []);
  const sorry = `${nat}let t = sorry(T : Type());\ninspect;\nlet u = { let w = sorry(x : t); Zero() };\ninspect;\n`;
  assert.deepEqual(check(sorry, 1).inspects.map(i => scopeOf(i.info)), [["t : Type()"], ["t : Type()", "u : Nat() is Zero()"]]);
  const isSucc = "data IsSucc(n : Nat()) : Type() {\n  IsSuccHere(m : Nat()) : IsSucc(Succ(m));\n}\n";
  const given = `${nat}${isSucc}let k = sorry(k : Nat());\nlet p = sorry(p : IsSucc(k));\nlet IsSuccHere(_) = p;\n` +
    "fn f() -> (r : IsSucc(k)) { sorry(_) }\n";
  const g = check(given, 1), inF = g.infoAt(at(given, "sorry(_)"));
  assert.equal(g.error, null);
  assert.deepEqual([inF.expected.entries?.[0]?.type?.text, scopeOf(inF)],
    ["IsSucc(Succ(_@10:16))", ["_@10:16 : Nat()"]]);
});

test("nameAt: what each name occurrence refers to", () => {
  const r = check(front, 1);
  assert.equal(r.error, null);
  assert.equal(named(r, at(front, "x : A)")), "entry x : A");
  assert.equal(named(r, at(front, "x);")), "entry x : Vec(Nat(), Succ(Zero())) is VCons(Nat(), Zero(), Zero(), VNil(Nat()))");
  assert.equal(named(r, at(front, "hd, _)")), "entry hd : A");
  assert.equal(named(r, at(front, "hd\n}")), "entry hd : A");
  assert.equal(named(r, at(front, "v : Vec(A, Succ")), "entry v : Vec(A, Succ(n))");
  assert.equal(named(r, at(front, "VCons(_")), "ctor VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n))");
  assert.equal(named(r, at(front, "VCons(A : Type()")), "ctor VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n))");
  assert.equal(named(r, at(front, "Vec(A : Type(), n")), "type Vec(A : Type(), n : Nat()) : Type()");
  assert.equal(named(r, at(front, "Nat(), Zero(), Zero()")), "type Nat() : Type()");
  assert.equal(named(r, at(front, "vhead(Nat")), "fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A)");
  assert.equal(named(r, at(front, "vhead(A")), named(r, at(front, "vhead(Nat")));
  assert.equal(r.nameAt(at(front, "let VCons", 1)), null);
  assert.equal(r.nameAt(at(front, "VCons(_, _", 6)), null);
  const local = `${nat}fn f(n : Nat()) -> (r : Nat()) { let g = n; g }\nfn g(m : Nat()) -> (r : Nat()) { m }\n`;
  const l = check(local, 1);
  assert.equal(named(l, at(local, "g }")), "entry n,g : Nat()");
  assert.equal(named(l, at(local, "g = n")), "entry n,g : Nat()");
  assert.equal(named(l, at(local, "g(m")), "fn g(m : Nat()) -> (r : Nat())");
  const goal = `${nat}goal fn (a : Nat()) -> (b : Nat());\nfn f(n : Nat()) -> (r : Nat()) { n }\nqed f;\n`;
  assert.equal(named(check(goal, 1), at(goal, "f;")), "fn f(n : Nat()) -> (r : Nat())");
  assert.equal(named(check(goal, 1), at(goal, "a : Nat()")), "entry a : Nat()");
  const broken = `${nat}fn f(n : Nat()) -> (r : Nat()) { Succ(Nat()) }\nprint f(Zero());\nlet z = Zero();\n`;
  const b = check(broken, 1);
  assert.match(b.error?.message() ?? "", /must have type/);
  assert.equal(b.nameAt(at(broken, "f(Zero")), null);
  assert.equal(b.nameAt(at(broken, "z =")), null);
  assert.equal(named(b, at(broken, "n : Nat()")), "entry n : Nat()");
});
