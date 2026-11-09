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

const eqData = "data Eq(A : Type(), x : A, y : A) : Type() {\n  Refl(A : Type(), x : A) : Eq(A, x, x);\n}\n";
const plusData = "data Plus(m : Nat(), n : Nat(), r : Nat()) : Type() {\n  PlusZero(n : Nat()) : Plus(Zero(), n, n);\n  PlusSucc(m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r)) : Plus(Succ(m), n, Succ(r));\n}\n";
const plusZero = `fn plusZero(subterm n : Nat(), r : Nat(), p : Plus(n, Zero(), r)) -> (e : Eq(Nat(), r, n)) {
  match p : _ {
    PlusZero(_) => Refl(Nat(), r);
    PlusSucc(m, _, r1, q) => match plusZero(subterm m, r1, q) : _ {
      Refl(_, _) => Refl(Nat(), r);
    };
  }
}
`;
const plusGoal = (goal: string): string => `${nat}${eqData}${plusData}goal fn ${goal};\n${plusZero}qed plusZero;\n`;
const falseData = "data False() : Type() {}\n";
const verdicts = (r: CheckResult) => [r.containsSorry, r.qedChecks, r.goalProved];

test("function goals: plusZero proves the goal, binder names and subterm marks aside", () => {
  const source = plusGoal("(n : Nat(), r : Nat(), p : Plus(n, Zero(), r)) -> (e : Eq(Nat(), r, n))");
  const r = ok(source);
  assert.deepEqual(verdicts(r), [false, true, true]);
  const at = r.infoAt(offset(source, "qed plusZero", 5)).expected;
  assert.deepEqual([at?.params?.map(e => `${e.name} : ${e.type?.text}`), at?.entries?.map(e => `${e.name} : ${e.type?.text}`)],
    [["n : Nat()", "r : Nat()", "p : Plus(n, Zero(), r)"], ["e : Eq(Nat(), r, n)"]]);
  const inGoal = offset(source, "Eq(Nat(), r, n));", 10);
  assert.deepEqual(scopeOf(r.infoAt(inGoal)), ["n : Nat()", "r : Nat()", "p : Plus(n, Zero(), r)"]);
  assert.equal(r.infoAt(inGoal).termination, null);
  const p = r.evalAt(inGoal, "p");
  if ("error" in p) assert.fail(p.error.message());
  assert.equal(p.type.text, "Plus(n, Zero(), r)");
  assert.equal(r.explainAt(inGoal)?.canonical.text, "r");
  assert.deepEqual(verdicts(ok(plusGoal("(a : Nat(), b : Nat(), _ : Plus(a, Zero(), b)) -> (_ : Eq(Nat(), b, a))"))), [false, true, true]);
});

test("function goals: a telescope that differs does not prove the goal", () => {
  const mismatch = (goal: string, pattern: RegExp) => {
    const source = plusGoal(goal);
    err(source, "plusZero", pattern, "qed plusZero");
    assert.deepEqual(verdicts(check(source, 1)), [false, false, false]);
  };
  mismatch("(n : Nat(), r : Nat(), p : Plus(n, Zero(), r)) -> (e : Eq(Nat(), n, r))",
    /plusZero's return 1 is `e : Eq\(Nat\(\), r, n\)`, and the goal's is `e : Eq\(Nat\(\), n, r\)`.*canonically identical/);
  mismatch("(n : Nat(), r : Nat(), p : Plus(r, Zero(), n)) -> (e : Eq(Nat(), r, n))",
    /plusZero's parameter 3 is `p : Plus\(n, Zero\(\), r\)`, and the goal's is `p : Plus\(r, Zero\(\), n\)`/);
  mismatch("(n : Nat(), r is Zero(), p : Plus(n, Zero(), r)) -> (e : Eq(Nat(), r, n))", /plusZero's parameter 2 is `r : Nat\(\)`, and the goal's is `r is Zero\(\)`/);
  mismatch("(n : Nat(), p : Plus(n, Zero(), n)) -> (e : Eq(Nat(), n, n))", /plusZero has 3 parameters and 1 return, and the goal has 2 parameters and 1 return/);
  mismatch("(r : Nat(), n : Nat(), _ : Plus(n, Zero(), r)) -> (e : Eq(Nat(), r, n))",
    /plusZero's parameter 3 is `_ : Plus\(r, Zero\(\), n\)`, and the goal's is `_ : Plus\(n, Zero\(\), r\)` \(binders named as in the goal\)/);
  assert.deepEqual(verdicts(ok(plusGoal("(r : Nat(), n : Nat(), _ : Plus(r, Zero(), n)) -> (e : Eq(Nat(), n, r))"))), [false, true, true]);
});

test("function goals: the Expected panel shows the goal at a `qed` naming a function, on the error path too", () => {
  const fn = `${nat}fn f(n : Nat()) -> (r : Nat()) { n }\n`, typeGoal = `${fn}goal Nat();\nqed f;\n`;
  assert.deepEqual(check(typeGoal, 1).infoAt(offset(typeGoal, "f;")).expected?.entries?.map(e => e.type?.text), ["Nat()"]);
  const fnGoal = `${fn}goal fn (m : Nat()) -> (r : Nat());\nqed f;\n`;
  assert.deepEqual(ok(fnGoal).infoAt(offset(fnGoal, "f;")).expected?.params?.map(e => e.type?.text), ["Nat()"]);
});

test("function goals: telescopes are compared with bound variables, an earlier is clause not in force (D47)", () => {
  const goal = `${nat}${eqData}goal fn (n is Zero(), e : Eq(Nat(), n, Zero())) -> (r : Nat());\n`;
  const source = `${goal}fn f(m is Zero(), e : Eq(Nat(), Zero(), m)) -> (r : Nat()) { m }\nqed f;\n`;
  err(source, "f", /f's parameter 2 is `e : Eq\(Nat\(\), Zero\(\), n\)`, and the goal's is `e : Eq\(Nat\(\), n, Zero\(\)\)`/, "qed f");
  assert.deepEqual(verdicts(check(source, 1)), [false, false, false]);
  assert.deepEqual(verdicts(ok(`${goal}fn f(m is Zero(), e : Eq(Nat(), m, Zero())) -> (r : Nat()) { m }\nqed f;\n`)), [false, true, true]);
});

test("function goals: taint, sorry and the identity on False()", () => {
  const sorry = ok(`${falseData}goal fn () -> (r : False());\nfn f() -> (r : False()) { sorry(_) }\nqed f;\n`);
  assert.deepEqual(verdicts(sorry), [true, true, false]);
  const viaCall = ok(`${falseData}goal fn () -> (r : False());\nfn g() -> (r : False()) { sorry(_) }\nfn f() -> (r : False()) { g() }\nqed f;\n`);
  assert.deepEqual(verdicts(viaCall), [true, true, false]);
  const identity = ok(`${falseData}goal fn (p : False()) -> (r : False());\nfn id(q : False()) -> (s : False()) { q }\nqed id;\n`);
  assert.deepEqual(verdicts(identity), [false, true, true]);
  const taintedGoal = ok(`${nat}let T = sorry(x : Type());\ngoal fn (x : T) -> (r : T);\nfn f(y : T) -> (r : T) { y }\nqed f;\n`);
  assert.deepEqual(verdicts(taintedGoal), [true, true, false]);
  const poisoned = ok(`${nat}data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\ngoal fn (n : Nat()) -> (r : Nat());\nfn f(n : Nat()) -> (r : Nat()) { n }\nlet s = sorry(p : IsZero(Zero()));\nlet IsZeroHere() = s;\nqed f;\n`);
  assert.deepEqual(verdicts(poisoned), [true, true, false]);
});

test("function goals: qed names a function exactly when the goal is a function goal", () => {
  const fn = `${nat}fn f(n : Nat()) -> (r : Nat()) { n }\n`;
  err(`${fn}goal Nat();\nqed f;\n`, "f", /f is a function, and naming a function proves only a function goal.*this goal is a type/, "qed f");
  const fnGoal = `${nat}goal fn (n : Nat()) -> (r : Nat());\n`;
  err(`${fnGoal}qed Zero();\n`, "Zero()", /the goal is a function goal, so `qed` names a function declared before it/, "qed");
  err(`${fnGoal}let x = Zero();\nqed x;\n`, "x", /the goal is a function goal/, "qed x");
  err(`${fnGoal}qed f;\nfn f(n : Nat()) -> (r : Nat()) { n }\n`, "f", /the goal is a function goal/, "qed f");
  err(`${nat}goal fn (n : Nat()) -> (n : Nat());\n`, "n", /already in scope/, "-> (n");
  err(`${nat}goal fn (n : Nat()) -> (r : Succ(n));\n`, "Succ(n)", /not a type/);
});

test("function goals in phase 2: multiplicities must match", () => {
  const source = (mult: string) => `${nat}goal fn (erased n : Nat()) -> (r : Nat());\nfn f(${mult}n : Nat()) -> (r : Nat()) { Zero() }\nqed f;\n`;
  const proved = check(source("erased "), 2);
  assert.equal(proved.error, null);
  assert.deepEqual(verdicts(proved), [false, true, true]);
  const differs = check(source(""), 2);
  assert.match(differs.error?.message() ?? "", /f's parameter 1 is `n : Nat\(\)`, and the goal's is `erased n : Nat\(\)`/);
  assert.deepEqual(verdicts(differs), [false, false, false]);
});

test("tuple let binders are a telescope, checked against the results they name (D44)", () => {
  const f = "fn f(A : Type(), x : Nat()) -> (n : Nat(), v : Vec(A, n)) { (Zero(), VNil(A)) }\n";
  ok(`${nat}${vec}${f}fn g(A : Type(), x : Nat()) -> (r : Nat()) {\n  let (m : Nat(), v : Vec(A, m)) = f(A, x);\n  m\n}\n`);
  const untyped = /`m` has no type here: give it one before referring to it/;
  err(`${nat}${vec}${f}fn g(A : Type(), x : Nat()) -> (r : Nat()) {\n  let (m, v : Vec(A, m)) = f(A, x);\n  m\n}\n`, "m", untyped, "A, m)");
  err(`${nat}let (m, w is Succ(m)) = (Zero(), Succ(Zero()));\n`, "m", untyped, "Succ(m)");
  err(`${nat}let (m, k : Nat(), w is Succ(Succ(m))) = sorry(_);\n`, "m", untyped, "Succ(m)");
  assert.deepEqual(ok(`${nat}let (m : Nat(), w is Succ(m)) = (Zero(), Succ(Zero()));\nprint w;\n`).prints.map(p => p.value), [nats(1)]);
  err(`${nat}let (m : Nat(), w is Succ(m)) = (Zero(), ${nats(2)});\n`, nats(2), /`w` must be Succ\(Zero\(\)\), and this is Succ\(Succ\(Zero\(\)\)\)/);
  err(`${nat}let (m : Nat(), w is Succ(m)) = (Zero(), Zero());\n`, "Zero()", /`w` must be Succ\(Zero\(\)\), and this is Zero\(\)/, ", Zero());");
  err(`${nat}${vec}let (m : Type(), w : Vec(Nat(), m)) = (Nat(), VNil(Nat()));\n`, "m", /`n` must have type Nat\(\), and this has type Type\(\)/, "Nat(), m)");
  err(`${nat}let (m, w : Nat()) = sorry(_);\n`, "sorry(_)", /`_` stands for the whole telescope/);
  ok(`${nat}let (m : Nat(), w is Succ(m)) = sorry(_);\n`);
  ok(`${nat}let (m, w : Nat()) = (Zero(), Zero());\nprint m;\n`);
  err(`${nat}let (w is Succ(m), m : Nat()) = (Zero(), Zero());\n`, "m", /m is not in scope/);
  err(`${nat}let (m, m) = (Zero(), Zero());\n`, "m", /introduced twice/, ", m)");
  const source = `${nat}${vec}let (m : Nat(), v : Vec(Nat(), m)) = { let k = Zero(); (k, VNil(Nat())) };\n`;
  ok(source);
  err(source.replace("Vec(Nat(), m)", "Vec(Nat(), k)"), "k", /k is not in scope/);
});

const isZero = "data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\n";

test("a pattern let's facts and fields survive its block; only its names end there (D45)", () => {
  const source = `${nat}${vec}fn h(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (r : Vec(A, n)) {\n  let (t : Vec(A, n)) = { let VCons(_, _, _, r) = v; r };\n  inspect;\n  t\n}\n`;
  assert.deepEqual(scopeOf(ok(source).inspects[0]!.info), [
    "A : Type()", "n : Nat()", "v : Vec(A, Succ(n)) is VCons(A, n, ?VCons.head@10:43, t)",
    "?VCons.A : Type() is A", "?VCons.n : Nat() is n", "?VCons.head : A", "t : Vec(A, n)",
  ]);
  err(source.replace("  t\n}", "  r\n}"), "r", /r is not in scope/, "  r\n}");
  const isSucc = "data IsSucc(n : Nat()) : Type() {\n  IsSuccHere(m : Nat()) : IsSucc(Succ(m));\n}\n";
  const refuted = `${nat}${vec}${isSucc}fn h(A : Type(), k : Nat(), w : Vec(A, k), p : IsSucc(k)) -> (r : A) {\n  let x = { let IsSuccHere(j) = p; let VCons(_, _, hd, _) = w; hd };\n  inspect;\n  x\n}\n`;
  const after = scopeOf(ok(refuted).inspects[0]!.info);
  assert.ok(after.some(e => /^k : Nat\(\) is Succ\(\?IsSuccHere\.m@/.test(e)), after.join("; "));
  assert.ok(after.some(e => /^w : .* is VCons\(A, \?IsSuccHere\.m@[\d:]+, x, /.test(e)), after.join("; "));
  err(refuted.replace("let IsSuccHere(j) = p; ", ""), "VCons(_, _, hd, _)", /VNil is not refuted/);
});

test("a branch's facts end with the branch, a pattern let's in a block in it included", () => {
  err(`${nat}${vec}fn h(n : Nat(), v : Vec(Nat(), n)) -> (r : Nat()) {\n  let x = match n : (r : Nat()) { Zero() => Zero(); Succ(m) => { let VCons(_, _, hd, _) = v; hd }; };\n  let VCons(_, _, h2, _) = v;\n  h2\n}\n`,
    "VCons(_, _, h2, _)", /VNil is not refuted/);
});

test("soundness: a tainted pattern let in a block poisons the rest of the program (D45)", () => {
  const source = `${nat}${eqData}${isZero}fn mk() -> (n : Nat()) { Succ(Zero()) }\nlet n = mk();\nlet p = sorry(p : IsZero(n));\nprint n;\n` +
    "let x = { let IsZeroHere() = p; n };\nlet (y is Zero()) = n;\ngoal Eq(Nat(), n, Zero());\nqed Refl(Nat(), n);\nprint n;\nprint Zero();\n";
  const r = ok(source);
  assert.deepEqual(verdicts(r), [true, true, false]);
  assert.deepEqual(r.prints.map(p => p.value), [nats(1), "sorry", "sorry"]);
  const later = `${nat}${eqData}${isZero}fn mk() -> (n : Nat()) { Succ(Zero()) }\nlet n = mk();\nlet p = sorry(p : IsZero(n));\n` +
    "goal Eq(Nat(), n, Zero());\nlet (a, q : Eq(Nat(), n, Zero())) = ({ let IsZeroHere() = p; n }, Refl(Nat(), n));\nqed q;\n";
  assert.deepEqual(verdicts(ok(later)), [true, true, false]);
  const inFn = `${nat}${eqData}${isZero}fn f(n : Nat()) -> (q : Eq(Nat(), n, Zero())) {\n  let p = sorry(p : IsZero(n));\n` +
    `  let (a, q : Eq(Nat(), n, Zero())) = ({ let IsZeroHere() = p; n }, Refl(Nat(), n));\n  q\n}\ngoal Eq(Nat(), ${nats(1)}, Zero());\nqed f(${nats(1)});\n`;
  assert.deepEqual(verdicts(ok(inFn)), [true, true, false]);
});

test("soundness: a tainted pattern let in a match branch taints the match's results, and neither its taint nor its facts leave the branch (D45)", () => {
  const fab = `${nat}${eqData}${isZero}fn mk() -> (n : Nat()) { Succ(Zero()) }\nlet n = mk();\nlet b = mk();\n`;
  const m = "match b : (r : Nat()) { Zero() => Zero(); Succ(k) => { let IsZeroHere() = sorry(p : IsZero(n)); n }; }";
  const top = ok(`${fab}let c = ${m};\nprint c;\nprint n;\ngoal Nat();\nqed n;\n`);
  assert.deepEqual([verdicts(top), top.prints.map(p => p.value)], [[true, true, true], ["sorry", nats(1)]]);
  assert.deepEqual(verdicts(ok(`${fab}let c = ${m};\ngoal Nat();\nqed c;\n`)), [true, true, false]);
  err(`${fab}let c = ${m};\nlet (q : Eq(Nat(), n, Zero())) = Refl(Nat(), n);\n`, "Refl(Nat(), n)", /`q` must have type Eq\(Nat\(\), n, Zero\(\)\)/, "let (q");
  const fns = `${fab}fn g(x : Nat()) -> (r : Nat()) {\n  let c = ${m};\n  x\n}\nfn h(x : Nat()) -> (r : Nat()) {\n  let c = ${m};\n  c\n}\ngoal Nat();\n`;
  assert.deepEqual(verdicts(ok(`${fns}qed g(Zero());\n`)), [true, true, true]);
  assert.deepEqual(verdicts(ok(`${fns}qed h(Zero());\n`)), [true, true, false]);
});
