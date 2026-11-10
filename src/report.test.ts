import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "./check.ts";
import type { CheckResult } from "./api.ts";
import { file, globalEntriesOf, listed, nat, scopeOf, vecBy } from "../tests/helpers.ts";
import { position } from "./position.ts";
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
    ? `entry ${n.entry.names.join(",") || `?${n.entry.origin.kind}`} : ${n.entry.canonical.type.term.text}${n.entry.rule ? ` is ${n.entry.canonical.rule!.term.text}` : ""}`
    : `${n.kind} ${n.name}${n.signature.text}`;
};

test("a program whose last statement is unfinished keeps what precedes it checked", () => {
  const source = `${nat}let a = Succ(Zero());\nprint a;\nlet b = Succ(`;
  const r = check(source, 1);
  assert.equal(r.error?.span.start, source.length);
  assert.match(r.error?.message() ?? "", /expected an expression/);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())"]);
  const tail = r.infoAt(source.length);
  assert.deepEqual(tail.globals.map(g => g.name), ["Type", "Nat"]);
  assert.deepEqual(tail.globals[1]?.ctors?.map(c => c.name), ["Zero", "Succ"]);
  assert.deepEqual([globalEntriesOf(tail), scopeOf(tail)], [["?@5:14 : Nat() is Zero()", "a : Nat() is Succ(Zero())"], []]);
  assert.equal(named(r, at(source, "print a", 6)), "entry a : Nat() is Succ(Zero())");
  assert.equal(r.nameAt(source.length - 3), null);
  const e = r.evalAt(source.length, "Succ(a)");
  if ("error" in e) assert.fail(e.error.message());
  assert.equal(e.canonicalRule?.text, "Succ(Succ(Zero()))");
  const lexical = check(`${nat}print Zero();\nlet c = Zero(); é`, 1);
  assert.match(lexical.error?.message() ?? "", /non-ASCII/);
  assert.deepEqual([lexical.prints.length, lexical.infoAt(nat.length + 30).globalEntries.map(e => e.names)], [1, [[], ["c"]]]);
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

test("the entries a top-level statement created are global; Scope lists the rest, and none at the top level (§13)", () => {
  const source = `${nat}let a = Zero();\nfn f(n : Nat()) -> (r : Nat()) {\n  let m = Succ(n);\n  inspect;\n  m\n}\nlet b = f(a);\ninspect;\n`;
  const r = check(source, 1), split = (offset: number) => { const i = r.infoAt(offset); return [globalEntriesOf(i), scopeOf(i)]; };
  assert.deepEqual(r.inspects.map(i => [globalEntriesOf(i.info), scopeOf(i.info), i.info.topLevel]), [
    [["a : Nat() is Zero()"], ["?@6:10 : Type() is Nat()", "n : Nat()", "m : Nat() is Succ(n)"], false],
    [["a : Nat() is Zero()", "b : Nat()"], [], true],
  ]);
  assert.deepEqual(split(at(source, "n : Nat()")), [["a : Nat() is Zero()"], []]);
  assert.deepEqual(split(at(source, "\nlet b")), [["a : Nat() is Zero()"], []]);
});

test("every entry in scope is listed, named or not, in the order the entries were created (§13)", () => {
  const source = `${nat}${vec}fn f(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (r : A) {\n  let VCons(_, _, h, _) = v;\n  inspect;\n  h\n}\nprint f(Nat(), Zero(), VCons(Nat(), Zero(), Zero(), VNil(Nat())));\ninspect;\n`;
  const [body, after] = check(source, 1).inspects.map(i => i.info);
  assert.deepEqual(scopeOf(body!), ["?@10:10 : Type() is Type()", "A : Type()", "?@10:22 : Type() is Nat()", "n : Nat()",
    "?@10:40 : Nat() is Succ(n)", "?@10:33 : Type() is Vec(A, Succ(n))", "v : Vec(A, Succ(n)) is VCons(A, n, h, _@11:22)",
    "_@11:13 : Type() is A", "_@11:16 : Nat() is n", "h : A", "_@11:22 : Vec(A, n)"]);
  assert.deepEqual(globalEntriesOf(after!), ["?@15:9 : Type() is Nat()", "?@15:16 : Nat() is Zero()", "?@15:30 : Type() is Nat()",
    "?@15:37 : Nat() is Zero()", "?@15:45 : Nat() is Zero()", "?@15:58 : Type() is Nat()",
    "?@15:53 : Vec(Nat(), Zero()) is VNil(Nat())",
    "?@15:24 : Vec(Nat(), Succ(Zero())) is VCons(Nat(), Zero(), Zero(), VNil(Nat()))", "?@15:7 : Nat()"]);
  const sorry = `${nat}let t = sorry(T : Type());\ninspect;\nlet u = { let w = sorry(x : t); Zero() };\ninspect;\n`;
  assert.deepEqual(check(sorry, 1).inspects.map(i => globalEntriesOf(i.info)),
    [["t : Type()"], ["t : Type()", "?@7:19 : t", "u : Nat() is Zero()"]]);
  const isSucc = "data IsSucc(n : Nat()) : Type() {\n  IsSuccHere(m : Nat()) : IsSucc(Succ(m));\n}\n";
  const given = `${nat}${isSucc}let k = sorry(k : Nat());\nlet p = sorry(p : IsSucc(k));\nlet IsSuccHere(_) = p;\n` +
    "fn f() -> (r : IsSucc(k)) { sorry(_) }\n";
  const g = check(given, 1), inF = g.infoAt(at(given, "sorry(_)"));
  assert.equal(g.error, null);
  assert.deepEqual([inF.expected.entries?.[0]?.canonical.type?.term.text, scopeOf(inF), globalEntriesOf(inF)],
    ["IsSucc(Succ(_@10:16))", [], ["k : Nat() is Succ(_@10:16)", "p : IsSucc(Succ(_@10:16)) is IsSuccHere(_@10:16)",
      "_@10:16 : Nat()"]]);
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

test("the dialog's data: raw form, the rules applied written with an arrow, and how each rule was made (§13)", () => {
  const source = file("sort.pledge", "examples"), r = check(source, 2), where = position(source);
  const info = r.infoAt(at(source, "(Cons(y, zs), InsThere")), entry = (n: string) => listed(info).find(e => e.names.includes(n))!;
  const p = entry("p"), steps = p.canonical.type.rewrites();
  assert.deepEqual([p.type.text, p.canonical.type.term.text], ["Le(_@132:16, _@132:13)", "Le(y, x)"]);
  assert.deepEqual(steps.map(s => [s.rule.text, where(s.at.start), s.to.text]),
    [["_@132:13 → x", "132:7", "Le(_@132:16, x)"], ["_@132:16 → y", "132:7", "Le(y, x)"]]);
  assert.deepEqual(steps[0]!.how().map(l => l.text), [
    "match ?@129:28 { GeOrd(_@132:13, _@132:16, p) => ... }",
    "1. Order(x, y) = Order(_@132:13, _@132:16)   (the scrutinee's type and GeOrd's)",
    "2. x = _@132:13   (argument 1 of Order in 1), so _@132:13 is x",
  ]);
  assert.deepEqual(entry("s").canonical.type.rewrites().map(s => s.how()[0]?.text), ["match xs { Cons(y, rest) => ... }"]);
  const expected = info.expected.entries!.find(e => e.name === "i")!;
  assert.deepEqual([expected.type?.text, expected.canonical.type?.term.text], ["Insert(x, xs, ys)", "Insert(x, Cons(y, rest), ys)"]);
  const lets = `${nat}let one = Succ(Zero());\nlet two = Succ(one);\n`;
  const two = check(lets, 1).infoAt(lets.length).globalEntries.find(e => e.names.includes("two"))!;
  assert.deepEqual([two.rule?.text, two.canonical.rule?.term.text], ["Succ(one)", "Succ(Succ(Zero()))"]);
  assert.deepEqual(two.canonical.rule!.rewrites().map(s => [s.rule.text, s.how().map(l => l.text)]),
    [["one → Succ(Zero())", ["one is Succ(Zero()): the entry of an application is that application (§7)"]]]);
  const hole = `${nat}${vec}let v = VCons(_, Zero(), Zero(), VNil(_));\nlet w = v;\n`;
  const v = check(hole, 1).infoAt(at(hole, "let w")).globalEntries.find(e => e.names.includes("v"))!;
  assert.deepEqual(v.canonical.type.rewrites().map(s => s.how().map(l => l.text)),
    [["1. _@10:15 = Nat()   (solving a `_` (§20)), so _@10:15 is Nat()"]]);
});

test("where an entry's rule was made and its type defined, against where the entry was created (§13)", () => {
  const source = file("sort.pledge", "examples"), r = check(source, 2), where = position(source);
  const info = r.infoAt(at(source, "(Cons(y, zs), InsThere"));
  const places = (n: string) => {
    const e = listed(info).find(x => x.names.includes(n) || x.marker === n)!;
    return [where(e.origin.span.start), e.ruleAt && where(e.ruleAt.start), where(e.typeAt.start)];
  };
  assert.deepEqual(places("xs"), ["122:22", "129:5", "122:22"]);
  assert.deepEqual(places("y"), ["129:10", null, "64:8"]);
  assert.deepEqual(places("?@122:15"), ["122:15", "122:15", "19:1"]);
  const types = `${nat}let t = Type();\nlet z = Zero();\nlet w = t;\n`, ti = check(types, 1).infoAt(at(types, "let w")), tw = position(types);
  assert.deepEqual(ti.globalEntries.map(e => [e.names.join(","), tw(e.origin.span.start), tw(e.typeAt.start)]),
    [["t", "5:9", "5:9"], ["z", "6:9", "2:12"]]);
});

test("a refutation's derivation starts with suppose and its match or pattern let, as written (§13)", () => {
  const header = (source: string, needle: string, phase: 1 | 2 = 1) =>
    check(source, phase).infoAt(at(source, needle, 1)).refutations?.map(f => f.derivation()[0]?.text);
  const data = `${nat}${vecBy("erased ")}`;
  assert.deepEqual(header(`${nat}let Succ(m) = Succ(Zero());\n`, "let Succ"), ["suppose let Zero() = ?@5:15;"]);
  assert.deepEqual(header(`${nat}comptime let Succ(m) = Succ(Zero());\n`, "comptime"), ["suppose comptime let Zero() = ?@5:24;"]);
  assert.deepEqual(header(`${data}fn f(erased v : Vec(Nat(), Zero())) -> (r : Nat()) {\n  let erased VNil(_) = v;\n  Zero()\n}\n`, "let erased", 2),
    ["suppose let erased VCons(@A, @n, @head, @rest) = v;"]);
});
