import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { check } from "./check.ts";
import type { CheckResult, EntryInfo, PositionInfo } from "./api.ts";

const testsDir = new URL("../tests/", import.meta.url);
const file = (name: string): string => readFileSync(new URL(name, testsDir), "utf8");
const nat = "data Nat() : Type() {\n  Zero() : Nat();\n  Succ(pred : Nat()) : Nat();\n}\n";
const vec = "data Vec(A : Type(), n : Nat()) : Type() {\n  VNil(A : Type()) : Vec(A, Zero());\n  VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));\n}\n";
const nats = (n: number): string => n === 0 ? "Zero()" : `Succ(${nats(n - 1)})`;

const ok = (source: string): CheckResult => {
  const r = check(source, 1);
  if (r.error) assert.fail(`unexpected error at ${r.error.span.start} (${JSON.stringify(source.slice(r.error.span.start, r.error.span.end))}): ${r.error.message()}`);
  return r;
};

const err = (source: string, at: string, pattern: RegExp, after = ""): string => {
  const r = check(source, 1);
  if (!r.error) return assert.fail("expected an error");
  const start = source.indexOf(at, after ? source.indexOf(after) : 0);
  assert.ok(start >= 0, `${at} is not in the source`);
  const message = r.error.message();
  assert.equal(source.slice(r.error.span.start, r.error.span.end), at, message);
  assert.equal(r.error.span.start, start, message);
  assert.match(message, pattern);
  assert.doesNotMatch(message, /internal|undefined|\[object/);
  return message;
};

const offset = (source: string, needle: string, delta = 0): number => {
  const i = source.indexOf(needle);
  assert.ok(i >= 0, `${needle} is not in the source`);
  return i + delta;
};

const entryText = (e: EntryInfo): string => `${e.names.join(",") || `?${e.origin.kind}`} : ${e.type.text}${e.rule ? ` is ${e.rule.text}` : ""}`;
const scopeOf = (info: PositionInfo): string[] => info.scope.map(entryText);

const option = "data Option(A : Type()) : Type() {\n  None(A : Type()) : Option(A);\n  Some(A : Type(), x : A) : Option(A);\n}\n";
const evenOdd = file("design_even_odd.pledge").slice(nat.length);
const decide = `${nat}${evenOdd}${option}
mutual {
  fn decideEven(subterm n : Nat()) -> (r : Option(Even(n))) {
    match n : (r : Option(Even(n))) {
      Zero() => Some(Even(n), EvenZero());
      Succ(m) => match decideOdd(subterm m) : (r : Option(Even(n))) {
        None(_) => None(Even(n));
        Some(_, q) => Some(Even(n), EvenSucc(m, q));
      };
    }
  }
  fn decideOdd(subterm n : Nat()) -> (r : Option(Odd(n))) {
    match n : (r : Option(Odd(n))) {
      Zero() => None(Odd(n));
      Succ(m) => match decideEven(subterm m) : (r : Option(Odd(n))) {
        None(_) => None(Odd(n));
        Some(_, q) => Some(Odd(n), OddSucc(m, q));
      };
    }
  }
}
`;

test("every tests/design_*.pledge checks with no error", () => {
  const files = readdirSync(testsDir).filter(f => f.startsWith("design_") && f.endsWith(".pledge"));
  assert.ok(files.length >= 10);
  for (const f of files) ok(file(f));
});

test("print shows the value of ack(2, 1)", () => {
  const r = ok(`${file("design_ack.pledge")}\nprint ack(Succ(Succ(Zero())), Succ(Zero()));\n`);
  assert.deepEqual(r.prints.map(p => p.value), [nats(5)]);
  assert.equal(r.containsSorry, false);
  assert.equal(r.qedChecks, null);
  assert.equal(r.goalProved, null);
});

test("proof by reflection with a mutual decideEven, proving a goal", () => {
  const source = `${decide}goal Even(${nats(2)});\ncomptime let Some(_, p) = decideEven(${nats(2)});\nprint p;\nqed p;\n`;
  const r = ok(source);
  assert.deepEqual(r.prints.map(p => p.value), [`EvenSucc(${nats(1)}, OddSucc(Zero(), EvenZero()))`]);
  const p = r.infoAt(offset(source, "print p", 6)).scope.find(e => e.names.includes("p"));
  assert.equal(p?.type.text, `Even(${nats(2)})`);
  assert.deepEqual([r.containsSorry, r.qedChecks, r.goalProved], [false, true, true]);
  err(`${decide}let Some(_, p) = decideEven(${nats(2)});\n`, "Some(_, p)", /None is not refuted/);
  err(`${decide}comptime let Some(_, p) = decideEven(${nats(1)});\n`, `decideEven(${nats(1)})`, /evaluates to None\(Even\(Succ\(Zero\(\)\)\)\), which is not headed by Some/);
});

test("a goal proved without sorry", () => {
  const r = ok(`${nat}goal Nat();\nqed Succ(Zero());\n`);
  assert.deepEqual([r.containsSorry, r.qedChecks, r.goalProved], [false, true, true]);
});

test("names: no shadowing, no keyword, one namespace", () => {
  err(`${nat}let x = Zero();\nlet x = Succ(x);\n`, "x", /already in scope.*shadow/, "let x = Succ");
  err(`${nat}let Nat = Zero();\n`, "Nat", /already in scope/, "let Nat");
  err(`${nat}fn f(f : Nat()) -> (r : Nat()) { f }\n`, "f", /already in scope/, "(f :");
  err(`${nat}let match = Zero();\n`, "match", /found keyword `match`/);
  err(`${nat}fn f(n : Nat()) -> (r : Nat()) { n }\nlet g = f;\n`, "f", /not first class/, "let g");
  err(`${nat}data P() : Type() { MkP(a : Nat(), a : Nat()) : P(); }\n`, "a", /twice/, ", a :");
});

test("type errors at the argument and at a tuple let binder's is clause", () => {
  err(`${nat}${vec}let v = VCons(Nat(), Zero(), Nat(), VNil(Nat()));\n`, "Nat()", /`head` must have type Nat\(\), and this has type Type\(\)/, "Zero(), Nat()");
  err(`${nat}let n = Zero();\nlet y is Succ(n) = n;\n`, "n", /`y` must be Succ\(Zero\(\)\), and this is Zero\(\)/, "= n;");
  err(`${nat}fn f(n : Nat()) -> (r : Nat()) { n }\nprint f((Zero(), Zero()));\n`, "(Zero(), Zero())", /1 value expected here/);
});

test("matching: refuted branches, missing branches, survivors and scrutinees", () => {
  const vfn = (body: string) => `${nat}${vec}fn f(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (r : Nat()) {\n  ${body}\n}\n`;
  const refuted = err(vfn("match v : (r : Nat()) { VNil(_) => Zero(); VCons(_, _, _, _) => Zero(); }"), "VNil(_)", /VNil is refuted here/);
  assert.match(refuted, /Succ and Zero are different heads/);
  err(vfn("match n : (r : Nat()) { Zero() => Zero(); }"), "match n : (r : Nat()) { Zero() => Zero(); }", /no branch for Succ/);
  err(vfn("let Succ(m) = n;\n  m"), "Succ(m)", /Zero is not refuted/);
  err(vfn("match A : (r : Nat()) {}"), "A", /Type\(\) cannot be the scrutinee/, "match A");
  err(`${nat}fn f(A : Type(), x : A) -> (r : Nat()) { match x : (r : Nat()) {} }\n`, "x", /not a data type/, "match x");
  err(vfn("match n : (r : Nat()) { Zero() => Zero(); Succ() => Zero(); }"), "Succ()", /1 field/);
});

test("termination marks follow §9 exactly", () => {
  const ack = file("design_ack.pledge");
  err(ack.replace("ack(subterm m1, Succ(Zero()))", "ack(m1, Succ(Zero()))"), "ack(m1, Succ(Zero()))", /marks one of ack's `subterm` parameters/);
  err(ack.replace("ack(same m, subterm n1)", "ack(same m1, subterm n1)"), "same m1", /m1 is not canonically identical to m/);
  err(ack.replace("ack(subterm m1, Succ(Zero()))", "ack(subterm m, Succ(Zero()))"), "subterm m", /is not a strict subterm of m/, "Zero() => ack(");
  const two = `${nat}mutual {\n  fn g(subterm n : Nat()) -> (r : Nat()) { match n : (r : Nat()) { Zero() => Zero(); Succ(m) => h(same n, subterm m); } }\n  fn h(subterm a : Nat(), subterm b : Nat()) -> (r : Nat()) { Zero() }\n}\n`;
  err(two, "h(same n, subterm m)", /g has only 1 `subterm` parameter/);
  ok(ack.replace("ack(subterm m1, ack(same m, subterm n1))", "ack(same m, subterm n1)"));
  err(`${nat}fn f(n : Nat()) -> (r : Nat()) { g(n) }\nfn g(n : Nat()) -> (r : Nat()) { n }\n`, "g", /g is not in scope/);
  err(`${nat}print Succ(subterm Zero());\n`, "subterm Zero()", /only a call within its group has marks/);
  err(`${nat}fn f(subterm n : Nat()) -> (r : Nat()) { n }\nprint f(subterm Zero());\n`, "subterm Zero()", /only a call within its group/);
  err(`${nat}fn f(n : Nat()) -> (r : Type()) { Nat() }\nfn g(x : f(Zero())) -> (r : Nat()) { Zero() }\n`, "f(Zero())", /contains no function call/);
});

test("goal and qed: at most once each, qed after goal", () => {
  const r = check(`${nat}qed Zero();\ngoal Nat();\n`, 1);
  assert.equal(r.error?.span.start, nat.length);
  assert.match(r.error?.message() ?? "", /`qed` comes after `goal`/);
  assert.deepEqual([r.qedChecks, r.goalProved], [false, false]);
  err(`${nat}goal Nat();\ngoal Nat();\n`, "goal Nat();", /at most one `goal`/, "Nat();\ngoal");
  err(`${nat}goal Nat();\nqed Nat();\n`, "Nat()", /must have type Nat\(\)/, "qed");
});

test("sorry: qed sorry(_) checks but proves nothing", () => {
  const r = ok("data False() : Type() {}\ngoal False();\nqed sorry(_);\n");
  assert.deepEqual([r.containsSorry, r.qedChecks, r.goalProved], [true, true, false]);
  err(`${nat}fn f(n : Nat()) -> (r : Nat()) { Succ(sorry(_)) }\n`, "sorry(_)", /`_` stands for the whole telescope/);
});

test("taint survives laundering through a function (D24's shape)", () => {
  const base = `${nat}data False() : Type() {}\ngoal False();\nlet b = sorry(x : False());\n`;
  const renamed = ok(`${base}fn id(p : False()) -> (r : False()) { let q = p; q }\nfn g(n : Nat()) -> (r : Nat()) { let y = b; n }\nprint g(Zero());\nqed id(b);\n`);
  assert.deepEqual(renamed.prints.map(p => p.value), ["Zero()"]);
  assert.deepEqual([renamed.containsSorry, renamed.qedChecks, renamed.goalProved], [true, true, false]);
  const used = ok(`${base}fn f() -> (r : False()) { b }\nqed f();\n`);
  assert.deepEqual([used.qedChecks, used.goalProved], [true, false]);
  const goalTainted = ok(`${nat}let T = sorry(x : Type());\ngoal T;\nqed sorry(_);\n`);
  assert.equal(goalTainted.goalProved, false);
});

test("print shows sorry for a tainted result, and only for it", () => {
  const r = ok(`${nat}let (a, b) = (Zero(), sorry(x : Nat()));\nprint a;\nprint b;\nprint Succ(b);\n`);
  assert.deepEqual(r.prints.map(p => p.value), ["Zero()", "sorry", "sorry"]);
});

test("after a tainted top-level pattern let, nothing evaluates and no goal is proved", () => {
  const source = `${nat}data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\ngoal Nat();\nlet s = sorry(p : IsZero(Zero()));\nprint Zero();\nlet IsZeroHere() = s;\nprint Zero();\nqed Zero();\n`;
  const r = ok(source);
  assert.deepEqual(r.prints.map(p => p.value), ["Zero()", "sorry"]);
  assert.deepEqual([r.containsSorry, r.qedChecks, r.goalProved], [true, true, false]);
});

test("a tainted comptime pattern let evaluates nothing", () => {
  const r = ok(`${decide}let n = sorry(x : Nat());\ncomptime let Some(_, p) = decideEven(n);\nprint Zero();\n`);
  assert.deepEqual(r.prints.map(p => p.value), ["sorry"]);
});

test("infoAt inside vhead's body: scope, expected and termination", () => {
  const source = file("design_vhead.pledge");
  const info = ok(source).infoAt(offset(source, "hd\n}", 1));
  assert.deepEqual(scopeOf(info), [
    "A : Type()", "n : Nat()", "v : Vec(A, Succ(n)) is VCons(A, n, hd, ?VCons.rest@12:23)",
    "?VCons.A : Type() is A", "?VCons.n : Nat() is n", "hd : A", "?VCons.rest : Vec(A, n)",
  ]);
  assert.deepEqual(info.expected?.entries?.map(e => [e.name, e.type?.text, e.undetermined]), [["x", "A", false]]);
  assert.deepEqual(info.termination, { fn: "vhead", subtermParams: [], group: ["vhead"] });
  assert.deepEqual(info.globals.map(g => g.name + g.signature.text), [
    "Type() : Type()", "Nat() : Type()", "Vec(A : Type(), n : Nat()) : Type()", "vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A)",
  ]);
  assert.deepEqual(info.globals[2]?.ctors?.map(c => c.name + c.signature.text), [
    "VNil(A : Type()) : Vec(A, Zero())", "VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n))",
  ]);
});

test("infoAt: termination inside ack, refutations at §10's inner match", () => {
  const ack = file("design_ack.pledge");
  const t = ok(ack).infoAt(offset(ack, "ack(same m", 5)).termination;
  assert.deepEqual(t, { fn: "ack", subtermParams: ["m", "n"], group: ["ack"] });
  const iz = file("design_iszero.pledge");
  const info = ok(iz).infoAt(offset(iz, "match p", 2));
  assert.deepEqual(info.refutations?.map(r => r.ctor), ["IsZeroHere"]);
  assert.deepEqual(info.refutations?.[0]?.derivation().map(l => l.text), [
    "1. IsZero(Succ(m)) = IsZero(Zero())   (the scrutinee's type and IsZeroHere's; rewritten by n)",
    "2. Succ(m) = Zero()   (argument 1 of IsZero in 1)",
    "refuted: Succ and Zero are different heads",
  ]);
  assert.deepEqual(ok(iz).infoAt(offset(iz, "match n", 2)).refutations, []);
  assert.equal(ok(iz).infoAt(offset(iz, "Zero() => Zero()", 12)).refutations, null);
});

test("infoAt: undetermined binders, nothing given, and globals with bindings", () => {
  const source = `${nat}let s = sorry(x : Nat());\nlet (a, b : Nat()) = (s, Zero());\nprint a;\n`;
  const r = ok(source);
  const at = r.infoAt(offset(source, "(s, Zero())"));
  assert.deepEqual(at.expected?.entries?.map(e => [e.name, e.type?.text ?? null, e.undetermined]), [["a", null, true], ["b", "Nat()", false]]);
  assert.equal(r.infoAt(offset(source, "print a", 6)).expected?.entries, null);
  assert.equal(r.infoAt(offset(source, "let s")).expected, null);
  const end = r.infoAt(source.length);
  assert.deepEqual(end.globals.filter(g => g.kind === "binding").map(g => g.name + g.signature.text), ["s : Nat()", "a : Nat()", "b : Nat() is Zero()"]);
  assert.deepEqual(end.scope.filter(e => e.tainted).map(e => e.names.join(",")), ["s,a"]);
});

test("inspect reports position information", () => {
  const source = `${nat}fn f(n : Nat()) -> (r : Nat()) {\n  let m = Succ(n);\n  inspect;\n  m\n}\n`;
  const r = ok(source);
  assert.equal(r.inspects.length, 1);
  assert.deepEqual(scopeOf(r.inspects[0]!.info), ["n : Nat()", "m : Nat() is Succ(n)"]);
});

test("explainAt gives the canonical form and the rewrites of a skeleton term", () => {
  const source = file("design_let_is.pledge");
  const r = ok(source);
  const ex = r.explainAt(offset(source, "= e;", 2));
  assert.equal(ex?.canonical.text, "Succ(Zero())");
  assert.deepEqual(ex?.rewrites.map(w => `${w.from.text} -> ${w.to.text}`), ["e -> Succ(n)", "Succ(n) -> Succ(Zero())"]);
  assert.equal(r.explainAt(offset(source, "Succ(n) = e"))?.canonical.text, "Succ(Zero())");
  assert.equal(r.explainAt(0), null);
});

test("evalAt checks typed text in the scope at a position", () => {
  const source = file("design_vuncons.pledge");
  const r = ok(source);
  const t = r.evalAt(source.length, "t");
  assert.ok(!("error" in t));
  if (!("error" in t)) assert.deepEqual([t.type.text, t.canonicalType.text, t.rule], ["Vec(A, n)", "Vec(Nat(), Zero())", null]);
  const v = r.evalAt(source.length, "VCons(A, n, h, t)");
  if ("error" in v) assert.fail(v.error.message());
  assert.deepEqual([v.type.text, v.canonicalType.text, v.rule?.text, v.canonicalRule?.text],
    ["Vec(A, Succ(n))", "Vec(Nat(), Succ(Zero()))", "VCons(A, n, h, t)", "VCons(Nat(), Zero(), h, t)"]);
  const bad = r.evalAt(source.length, "Succ(Nat())");
  assert.ok("error" in bad && bad.error.span.start === 5 && /must have type Nat\(\)/.test(bad.error.message()));
  const inBody = r.evalAt(offset(source, "(h, t)\n}"), "h");
  if ("error" in inBody) assert.fail(inBody.error.message());
  assert.equal(inBody.canonicalType.text, "A");
});
