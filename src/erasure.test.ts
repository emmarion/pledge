import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { check } from "./check.ts";
import type { CheckResult, EntryInfo, PositionInfo } from "./api.ts";
import type { Phase } from "./syntax.ts";

const testsDir = new URL("../tests/", import.meta.url);
const file = (name: string): string => readFileSync(new URL(name, testsDir), "utf8");
const nat = "data Nat() : Type() {\n  Zero() : Nat();\n  Succ(pred : Nat()) : Nat();\n}\n";
const vec = "data Vec(A : Type(), n : Nat()) : Type() {\n  VNil(erased A : Type()) : Vec(A, Zero());\n  VCons(erased A : Type(), erased n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));\n}\n";
const vhead = "fn vhead(erased A : Type(), erased n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {\n  let VCons(_, _, hd, _) = v;\n  hd\n}\n";
const eq = "data Eq(A : Type(), a : A, b : A) : Type() {\n  Refl(erased A : Type(), erased a : A) : Eq(A, a, a);\n}\n";

const ok = (source: string, phase: Phase = 2): CheckResult => {
  const r = check(source, phase);
  if (r.error) assert.fail(`unexpected error at ${JSON.stringify(source.slice(r.error.span.start, r.error.span.end))}: ${r.error.message()}`);
  return r;
};

const err = (source: string, at: string, pattern: RegExp, after = ""): void => {
  const r = check(source, 2);
  if (!r.error) return assert.fail("expected an error");
  const message = r.error.message();
  assert.equal(source.slice(r.error.span.start, r.error.span.end), at, message);
  assert.equal(r.error.span.start, source.indexOf(at, after ? source.indexOf(after) : 0), message);
  assert.match(message, pattern);
  assert.doesNotMatch(message, /internal|undefined|\[object/);
};

const prints = (r: CheckResult): string[] => r.prints.map(p => p.value);
const flagged = (info: PositionInfo): string[] => info.scope.filter(e => e.erased).map((e: EntryInfo) => e.names.join(",") || `?${e.origin.kind}`);
const leak = /is erased, and an erased value is allowed only in an erased position/;

test("the phase 2 example programs check and print erased fields as _", () => {
  assert.deepEqual(prints(ok(file("phase2_vec.pledge"))), [
    "Zero()", "VCons(_, _, Succ(Zero()), VCons(_, _, Zero(), VNil(_)))", "VCons(_, _, Zero(), VNil(_))",
  ]);
  assert.deepEqual(prints(ok(file("phase2_erased.pledge"))), [
    "Succ(Succ(Zero()))", "VCons(_, _, Zero(), VCons(_, _, Succ(Zero()), VNil(_)))", "Succ(Zero())",
  ]);
  const proof = ok(file("phase2_eq.pledge"));
  assert.deepEqual([proof.containsSorry, proof.qedChecks, proof.goalProved], [false, true, true]);
});

test("every tests/design_*.pledge checks under phase 2 as under phase 1", () => {
  const files = readdirSync(testsDir).filter(f => f.startsWith("design_") && f.endsWith(".pledge"));
  assert.ok(files.length >= 10);
  for (const f of files) {
    const outcome = (r: CheckResult) => [prints(r), r.qedChecks, r.goalProved, r.containsSorry];
    assert.deepEqual(outcome(ok(file(f), 2)), outcome(ok(file(f), 1)), f);
  }
});

test("in phase 1, erased is a plain name and nothing is erased", () => {
  const source = `${nat}fn f(erased : Nat(), many : Nat()) -> (r : Nat()) {\n  let x = Succ(erased);\n  inspect;\n  many\n}\n`;
  const r = ok(source, 1);
  assert.deepEqual(r.inspects[0]?.info.scope.map(e => [e.names.join(","), e.erased]), [["erased", false], ["many", false], ["x", false]]);
});

test("an erased name is an error outside an erased position, at the name", () => {
  err(`${nat}fn f(erased n : Nat()) -> (r : Nat()) { n }\n`, "n", leak, "{ n");
  err(`${nat}fn f(erased n : Nat()) -> (r : Nat()) { Succ(n) }\n`, "n", leak, "Succ(n");
  err(`${nat}fn f(erased n : Nat()) -> (r : Nat()) { let k = n; k }\n`, "n", leak, "= n");
  err(`${nat}fn g(m : Nat()) -> (r : Nat()) { m }\nfn f(erased n : Nat()) -> (r : Nat()) { g(n) }\n`, "n", leak, "g(n");
  err(`${nat}fn f(erased n : Nat()) -> (r : Nat()) { match n : (r : Nat()) { Zero() => Zero(); Succ(_) => Zero(); } }\n`, "n", leak, "match n");
  err(`${nat}let erased a = Zero();\nprint a;\n`, "a", leak, "print a");
  err(`${nat}let erased a = Zero();\ngoal Nat();\nqed a;\n`, "a", leak, "qed a");
  err(`${nat}fn f(erased n : Nat()) -> (erased r : Nat()) { n }\nprint f(Zero());\n`, "f(Zero())", leak);
  err(`${nat}fn f(n : Nat()) -> (erased a : Nat(), b : Nat()) { (n, n) }\nlet (x, y) = f(Zero());\n`, "f(Zero())", /value 1 of this is erased/, "let (x");
});

test("erased positions: types, erased parameters, fields and returns, and everything inside them", () => {
  const r = ok(`${nat}${vec}${eq}
fn f(erased n : Nat(), v : Vec(Nat(), n), erased w is Succ(n)) -> (erased m : Nat(), u : Vec(Nat(), n), p : Eq(Nat(), w, Succ(n))) {
  let (x : Vec(Nat(), n)) = v;
  let erased k = Succ(Succ(n));
  (Succ(match n : (r : Nat()) { Zero() => k; Succ(j) => j; }), x, Refl(Nat(), w))
}
fn g(erased A : Type()) -> (T : Type()) { Vec(A, Zero()) }
let (erased a, b, c) = f(Zero(), VNil(Nat()), Succ(Zero()));
print b;
print g(Nat());
print Vec(Nat(), Zero());
`);
  assert.deepEqual(prints(r), ["VNil(_)", "Vec(_, _)", "Vec(_, _)"]);
});

test("erased returns: a body whose results are all erased, and a block with mixed results", () => {
  const r = ok(`${nat}
fn twice(erased n : Nat()) -> (erased r : Nat()) { Succ(Succ(n)) }
fn both(erased n : Nat(), m : Nat()) -> (erased a : Nat(), b : Nat()) {
  let erased k = twice(n);
  (twice(k), Succ(m))
}
let (erased p, q) = both(Zero(), Zero());
let erased s = twice(p);
print q;
`);
  assert.deepEqual(prints(r), ["Succ(Zero())"]);
});

test("match erased: at most one branch with a many annotation entry", () => {
  const two = (ann: string) => `${nat}fn f(erased n : Nat()) -> (${ann}) {\n  match erased n : (${ann}) { Zero() => Zero(); Succ(m) => m; }\n}\n`;
  err(two("r : Nat()"), "Succ(m) => m;", /at most one branch/);
  ok(two("erased r : Nat()"));
  const one = `${nat}${vec}fn f(erased n : Nat(), v : Vec(Nat(), Succ(n)), w : Nat()) -> (r : Nat()) {\n  match erased v : (r : Nat()) { VCons(_, k, h, _) => w; }\n}\nprint f(_, VCons(_, _, Zero(), VNil(_)), Succ(Zero()));\n`;
  assert.deepEqual(prints(ok(one)), ["Succ(Zero())"]);
  const info = ok(one).infoAt(one.indexOf("w; }"));
  assert.deepEqual(flagged(info), ["n", "?VCons.A", "k", "h", "?VCons.rest"]);
  err(one.replace("=> w;", "=> h;"), "h", leak, "=> h");
});

const isZero = "data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\n";

test("match erased: absurd branches beside the one that is not (§16)", () => {
  const f = (branches: string) => `${nat}${isZero}fn f(n : Nat(), p : IsZero(n)) -> (r : Nat()) {\n  match erased n : (r : Nat()) {\n${branches}\n  }\n}\nprint f(Zero(), IsZeroHere());\n`;
  const source = f("    Zero() => Succ(Zero());\n    Succ(m) => match p : _ {};");
  const r = ok(source);
  assert.deepEqual(prints(r), ["Succ(Zero())"]);
  const at = r.infoAt(source.indexOf("match erased") + 2).refutations;
  assert.deepEqual(at?.map(x => [x.ctor, x.kind]), [["Succ", "absurd"]]);
  assert.deepEqual(r.infoAt(source.indexOf("match p") + 2).refutations?.map(x => [x.ctor, x.kind]), [["IsZeroHere", "refuted"]]);
  assert.deepEqual(prints(ok(f("    Succ(m) => { let q = p; inspect; match q : _ {} };\n    Zero() => Succ(Zero());"))), ["Succ(Zero())"]);
  err(f("    Zero() => Succ(Zero());\n    Succ(m) => Zero();"), "Succ(m) => Zero();", /at most one branch that is not absurd, a branch being absurd when its body is a match with no branches, possibly the final expression of a block/);
  err(f("    Zero() => match p : _ {};\n    Succ(m) => Zero();"), "match p : _ {}", /no branch for IsZeroHere, which is not refuted here/);
  const many = f("    Zero() => Succ(Zero());\n    Succ(m) => match p : _ {};").replace("match erased n", "match n");
  assert.deepEqual(ok(many).infoAt(many.indexOf("match n") + 2).refutations, []);
});

test("soundness: an absurd branch that relies on sorry taints the match, and an erased match whose branches are all absurd never runs (§16)", () => {
  const g = (pre: string, absurd: string) => `${nat}${isZero}${eq}fn g(n : Nat(), k : Nat(), p : IsZero(k)) -> (r : Nat()) {\n${pre}  match erased n : (r : Nat()) {\n` +
    `    Zero() => Succ(Zero());\n    Succ(m) => ${absurd};\n  }\n}\nprint g(Succ(Zero()), Zero(), IsZeroHere());\ngoal Nat();\nqed g(Succ(Zero()), Zero(), IsZeroHere());\n`;
  for (const [pre, absurd] of [
    ["", "match sorry(q : IsZero(Succ(m))) : _ {}"],
    ["  let (erased q : IsZero(Succ(Zero()))) = sorry(_);\n", "match erased q : _ {}"],
    ["", "{ let Refl(_, _) = sorry(e : Eq(Nat(), k, Succ(Zero()))); { match p : _ {} } }"],
  ]) {
    const r = ok(g(pre, absurd));
    assert.deepEqual([prints(r), r.goalProved], [["sorry"], false], absurd);
  }
  err(g("", "match erased Nat() : _ {}"), "Nat()", /cannot be the scrutinee/, "erased Nat");
  const never = `${nat}${isZero}fn h(n : Nat(), p : IsZero(Succ(n))) -> (r : Nat()) {\n  match erased n : (r : Nat()) {\n    Zero() => match p : _ {};\n    Succ(m) => match p : _ {};\n  }\n}\n` +
    "let (a, b) = (h(Zero(), sorry(q : IsZero(Succ(Zero())))), Zero());\nprint b;\nprint a;\n";
  assert.deepEqual(prints(ok(never)), ["Zero()", "sorry"]);
});

test("let erased: tuple binders and pattern lets bind erased; comptime cannot be erased", () => {
  const source = `${nat}${vec}let v = VCons(_, _, Zero(), VNil(_));\nlet (erased a, b) = (Succ(Zero()), Zero());\nlet erased c = b;\nlet erased VCons(x, y, z, w) = v;\nlet VCons(_, _, h, t) = v;\nprint VCons(x, y, h, t);\n`;
  const r = ok(source);
  assert.deepEqual(prints(r), ["VCons(_, _, Zero(), VNil(_))"]);
  assert.deepEqual(flagged(r.infoAt(source.length)), ["a", "x", "y", "z", "w", "?VCons.A", "?VCons.n"]);
  err(source.replace("print VCons(x, y, h, t)", "print VCons(x, y, z, t)"), "z", leak, "print");
  err(`${nat}comptime let erased Succ(p) = Succ(Zero());\n`, "comptime let erased Succ(p) = Succ(Zero());", /cannot be erased/);
});

test("_ stands for an erased argument, solved from later arguments and from what the position is given", () => {
  assert.deepEqual(prints(ok(`${nat}${vec}${vhead}print vhead(_, _, VCons(_, _, Zero(), VNil(_)));\n`)), ["Zero()"]);
  assert.deepEqual(prints(ok(`${nat}${vec}fn e() -> (v : Vec(Nat(), Zero())) { VNil(_) }\nprint e();\n`)), ["VNil(_)"]);
  const later = `${nat}${vec}fn g(erased A : Type(), v : Vec(A, Zero()), a : A) -> (r : A) { a }\nprint g(_, VNil(_), Succ(Zero()));\nprint g(_, { VNil(_) }, Zero());\n`;
  assert.deepEqual(prints(ok(later)), ["Succ(Zero())", "Zero()"]);
  const block = `${nat}${vec}fn g(erased A : Type(), v : Vec(A, Zero()), a : A) -> (r : A) { a }\nlet v = VNil(Nat());\nprint g(_, v, Zero());\nprint g(_, { v }, Zero());\nprint g(_, { let w = v; w }, Succ(Zero()));\n`;
  assert.deepEqual(prints(ok(block)), ["Zero()", "Zero()", "Succ(Zero())"]);
  const r = ok(`${nat}fn f(n : Nat(), erased m is Succ(n)) -> (r : Nat()) { n }\nprint f(Zero(), _);\n`);
  assert.deepEqual(prints(r), ["Zero()"]);
  const source = `${nat}${vec}let x = VCons(_, _, Zero(), VNil(_));\n`;
  assert.equal(ok(source).explainAt(source.indexOf("_"))?.canonical.text, "Nat()");
  assert.deepEqual(ok(source).infoAt(source.indexOf("_")).expected.entries?.map(e => [e.name, e.type?.text, e.erased]), [["A", "Type()", true]]);
});

test("explainAt shows a skeleton term with its _ solved", () => {
  const source = `${nat}${vec}fn g(erased A : Type(), v : Vec(A, Zero()), a : A) -> (r : A) { a }\nlet (z : Vec(Nat(), Zero())) = VNil(_);\nprint g(_, { VNil(_) }, Zero());\n`;
  const r = ok(source), nested = source.indexOf("VNil(_) }");
  assert.equal(r.explainAt(source.indexOf("VNil(_);") + 1)?.canonical.text, "VNil(Nat())");
  assert.equal(r.explainAt(nested + 1)?.canonical.text, "VNil(Nat())");
  assert.equal(r.explainAt(nested + 5)?.canonical.text, "Nat()");
});

test("_ is an error for a many parameter and where it cannot be inferred", () => {
  err(`${nat}${vec}print VCons(_, _, _, VNil(_));\n`, "_", /`head` of VCons is not erased/, "_, VNil");
  err(`${nat}fn f(n : Nat()) -> (r : Nat()) { n }\nprint f(_);\n`, "_", /`n` of f is not erased/);
  err(`${nat}${vec}print VNil(_);\n`, "_", /cannot be inferred/);
  err(`${nat}${vec}fn mk(erased B : Type()) -> (v : Vec(B, Zero())) { VNil(_) }\nlet x = mk(_);\n`, "_", /cannot be inferred/, "mk(_)");
});

test("soundness: unification gives a rule only to the entry of a _", () => {
  err(`${nat}${vec}${vhead}fn g(n : Nat(), v : Vec(Nat(), n)) -> (r : Nat()) { vhead(_, _, v) }\n`, "_", /cannot be inferred: it would need Succ\(\?_@\d+:\d+\) and n to be equal/, "_, v)");
  err(`${nat}${vec}fn g(n : Nat()) -> (v : Vec(Nat(), n)) { VNil(_) }\n`, "VNil(_)", /must have type Vec\(Nat\(\), n\)/);
  err(`${nat}${eq}fn bad(a : Nat(), b : Nat()) -> (q : Eq(Nat(), a, b)) { Refl(_, _) }\n`, "Refl(_, _)", /must have type Eq\(Nat\(\), a, b\)/);
  err(`${nat}${eq}goal Eq(Nat(), Succ(Zero()), Zero());\nqed Refl(_, _);\n`, "Refl(_, _)", /must have type/);
});

test("interface data shows multiplicities where written", () => {
  const source = `${nat}${vec}${vhead}`;
  const g = ok(source).infoAt(source.length).globals;
  assert.deepEqual(g.filter(x => x.kind === "fn").map(x => x.name + x.signature.text), ["vhead(erased A : Type(), erased n : Nat(), v : Vec(A, Succ(n))) -> (x : A)"]);
  assert.deepEqual(g.find(x => x.name === "Vec")?.ctors?.map(c => c.name + c.signature.text), [
    "VNil(erased A : Type()) : Vec(A, Zero())", "VCons(erased A : Type(), erased n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n))",
  ]);
  const inBody = ok(source).infoAt(source.indexOf("hd\n}"));
  assert.deepEqual(flagged(inBody), ["A", "n", "?VCons.A", "?VCons.n"]);
  assert.deepEqual(inBody.expected.entries?.map(e => [e.name, e.erased]), [["x", false]]);
});

const bad = "data Bad(n : Nat()) : Type() {\n  BadZero() : Bad(Zero());\n}\n";
const cast = "fn cast(erased m : Nat(), erased n : Nat(), erased p : Eq(Nat(), m, n), x : Bad(m)) -> (y : Bad(n)) {\n  match erased p : (y : Bad(n)) { Refl(_, _) => x; }\n}\n";
const absurd = "Eq(Nat(), Zero(), Succ(Zero()))";

test("soundness: every _ is solved, even when what the position is given mentions only the call's own results", () => {
  const pick = `${nat}${eq}${bad}${cast}fn pick(erased p : ${absurd}) -> (erased y is p, erased z is p) { (p, p) }\n`;
  const body = `${pick}fn bottom() -> (erased a : ${absurd}, erased b is a) { pick(_) }\n`;
  err(`${body}fn useit(x : Bad(Zero())) -> (y : Bad(Succ(Zero()))) {\n  let (erased a, erased b) = bottom();\n  cast(Zero(), Succ(Zero()), a, x)\n}\ngoal Bad(Succ(Zero()));\nqed useit(BadZero());\n`,
    "_", /cannot be inferred/, "pick(_)");
  err(`${pick}fn useit(x : Bad(Zero())) -> (y : Bad(Succ(Zero()))) {\n  let (erased a, erased b) = match x : (erased a : ${absurd}, erased b is a) { BadZero() => pick(_); };\n  cast(Zero(), Succ(Zero()), a, x)\n}\n`,
    "_", /cannot be inferred/, "pick(_)");
});

test("soundness: a _ is not solved by what is produced after it", () => {
  const own = `${nat}${eq}fn h(erased n : Nat()) -> (erased m : Nat(), erased p : Eq(Nat(), m, Succ(n))) { (Succ(n), Refl(_, _)) }\n` +
    "fn g() -> (erased m : Nat(), erased p : Eq(Nat(), m, Succ(m))) { h(_) }\n";
  err(own, "_", /mentions what is produced only after it/, "h(_)");
  err(`${nat}fn f(n : Nat()) -> (r : Nat()) { n }\nfn g(erased x : Nat(), y is x) -> (r : Nat()) { y }\nprint g(_, f(Zero()));\n`, "_", /mentions what is produced only after it/, "g(_");
});

test("taint: a _ whose solution mentions a tainted entry taints the application, as the written argument would", () => {
  const proof = (arg: string) => `${nat}${eq}${bad}${cast}let s = sorry(s : ${absurd});\n` +
    `fn cast2(erased q is s, x : Bad(Zero())) -> (y : Bad(Succ(Zero()))) { cast(Zero(), Succ(Zero()), q, x) }\ngoal Bad(Succ(Zero()));\nqed cast2(${arg}, BadZero());\n`;
  for (const arg of ["s", "_"]) assert.deepEqual([ok(proof(arg)).qedChecks, ok(proof(arg)).goalProved], [true, false], arg);
  const g = "fn g(erased A : Type(), v : Vec(A, Zero())) -> (w : Vec(A, Zero())) { v }\n";
  const at = (type: string, arg: string) => `${nat}${vec}${g}let T = sorry(T : Type());\nfn f(v : ${type}) -> (r : Nat()) { Zero() }\ngoal Nat();\nqed f(${arg});\nprint f(${arg});\n`;
  for (const arg of ["VNil(_)", "g(_, VNil(_))"]) {
    const tainted = ok(at("Vec(T, Zero())", arg)), clean = ok(at("Vec(Nat(), Zero())", arg));
    assert.deepEqual([tainted.goalProved, prints(tainted)], [false, ["sorry"]], arg);
    assert.deepEqual([clean.goalProved, prints(clean)], [true, ["Zero()"]], arg);
  }
  const source = `${nat}${vec}let T = sorry(T : Type());\nlet (y : Vec(T, Zero())) = VNil(_);\nlet (z : Vec(Nat(), Zero())) = VNil(_);\ninspect;\n`;
  assert.deepEqual(ok(source).inspects[0]?.info.scope.map(e => [e.names.join(","), e.tainted]), [["T", true], ["y", true], ["z", false]]);
});

test("taint: a _ is tainted only by an entry's own taint, never by its names (§12)", () => {
  const source = `${nat}${eq}fn mk() -> (n : Nat()) { Zero() }\nlet n = mk();\nlet s = sorry(s : Eq(Nat(), Zero(), Zero()));\nlet m = { let Refl(_, _) = s; n };\n` +
    "fn k(a : Nat(), erased b is a) -> (r : Nat()) { a }\nfn h1() -> (r : Nat()) {\n  let x = k(n, _);\n  inspect;\n  x\n}\nfn h2() -> (r : Nat()) {\n  let x = k(m, m);\n  inspect;\n  x\n}\n";
  const r = ok(source);
  assert.deepEqual(r.inspects.map(i => i.info.scope.filter(e => e.names.includes("x") || e.names.includes("m")).map(e => [e.names.join(","), e.tainted])),
    [[["n,m", true], ["x", false]], [["n,m", true], ["x", true]]]);
});
