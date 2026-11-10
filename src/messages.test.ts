import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "./check.ts";
import type { Phase } from "./syntax.ts";
import { file, nat } from "../tests/helpers.ts";

const says = (marked: string, message: string, phase: Phase = 1): void => {
  const start = marked.indexOf("⟦"), end = marked.indexOf("⟧") - 1;
  assert.ok(start >= 0 && end >= start, "mark where the error is with ⟦ ⟧");
  const source = marked.replace("⟦", "").replace("⟧", "");
  const error = check(source, phase).error;
  if (!error) return assert.fail("expected an error");
  assert.equal(error.message(), message);
  assert.deepEqual([error.span.start, error.span.end], [start, end], source.slice(error.span.start, error.span.end));
};

const derivation = (source: string, phase: Phase = 1): string[] =>
  check(source, phase).error?.derivation?.().map(l => l.text) ?? assert.fail("expected a refutation");

const eqFalse = "data Eq(A : Type(), x : A, y : A) : Type() {\n  Refl(A : Type(), x : A) : Eq(A, x, x);\n}\n" +
  "data False() : Type() {}\n";
const box = "data Box() : Type() {\n  B(x : Nat()) : Box();\n}\n";
const rule = "an erased value is allowed only in an erased position: a type, an argument for an erased parameter " +
  "or field, or the result for an erased return or binder (§16)";

test("a refutation's derivation lists the equation that gave each rule it was rewritten by", () => {
  const source = `${nat}${eqFalse}fn zeroNotOne(e : Eq(Nat(), Zero(), Succ(Zero()))) -> (f : False()) {
  match e : (f : False()) {
    Refl(_, x) => x;
  }
}
`;
  assert.deepEqual(derivation(source), [
    "Refl(_@11:10, x) =>",
    "1. Eq(Nat(), Zero(), Succ(Zero())) = Eq(_@11:10, x, x)   " +
      "(the scrutinee's type and Refl's)",
    "2. Zero() = x   (argument 2 of Eq in 1), so x is Zero()",
    "3. Succ(Zero()) = Zero()   (argument 3 of Eq in 1; rewritten by x, from 2)",
    "refuted: Succ and Zero are different heads",
  ]);
});

test("a derivation never names the anonymous entry of an application written in place", () => {
  assert.deepEqual(derivation(`${nat}let Succ(m) = Zero();\n`), [
    "Succ(m) =>",
    "1. Zero() = Succ(m)   (forcing Succ on the scrutinee)",
    "refuted: Zero and Succ are different heads",
  ]);
});

test("an erased value names the position it is not allowed in", () => {
  const leak = (what: string, position: string) => `${what} is erased, and ${position} is not; ${rule}`;
  const erasedN = "fn f(erased n : Nat()) -> (r : Nat()) ";
  says(`${nat}fn g(m : Nat()) -> (r : Nat()) { m }\n${erasedN}{ g(⟦n⟧) }\n`,
    leak("`n`", "parameter `m` of `g`"), 2);
  says(`${nat}${erasedN}{ Succ(⟦n⟧) }\n`, leak("`n`", "field `pred` of `Succ`"), 2);
  says(`${nat}${erasedN}{ ⟦n⟧ }\n`, leak("`n`", "return `r` of `f`"), 2);
  says(`${nat}let erased a = Zero();\nlet b = ⟦a⟧;\n`, leak("`a`", "binder `b`"), 2);
  says(`${nat}fn f(erased n : Nat(), m : Nat()) -> (r : Nat()) ` +
    "{ match m : (k : Nat()) { Zero() => ⟦n⟧; Succ(_) => n; } }\n",
    leak("`n`", "annotation entry `k`"), 2);
  says(`${nat}let erased a = Zero();\ngoal Nat();\nqed ⟦a⟧;\n`, leak("`a`", "the goal's proof"), 2);
  says(`${nat}${erasedN}{ match ⟦n⟧ : (r : Nat()) { Zero() => Zero(); Succ(_) => Zero(); } }\n`,
    leak("`n`", "the scrutinee of a `many` match"), 2);
  says(`${nat}${box}fn f(erased b : Box()) -> (r : Nat()) { let B(x) = ⟦b⟧; Zero() }\n`,
    leak("`b`", "the right-hand side of a `many` pattern `let`"), 2);
  says(`${nat}let erased a = Zero();\nprint ⟦a⟧;\n`, leak("`a`", "the expression of a `print`"), 2);
  says(`${nat}fn f(n : Nat()) -> (erased r : Nat()) { n }\nprint ⟦f(Zero())⟧;\n`,
    leak("this value", "the expression of a `print`"), 2);
});

test("a recursive call with no marks says what it must mark", () => {
  says(file("design_ack.pledge").replace("ack(subterm m1, Succ(Zero()))", "⟦ack(m1, Succ(Zero()))⟧"),
    "this call is within `ack`'s group, so it must mark one argument `subterm`: " +
    "the argument for one of `ack`'s `subterm` parameters (§9)");
  says(`${nat}mutual {\n  fn f(n : Nat()) -> (r : Nat()) { ⟦g(n)⟧ }\n  fn g(n : Nat()) -> (r : Nat()) { n }\n}\n`,
    "this call is within `g`'s group, so it must mark one argument `subterm`, " +
    "and `g` has no `subterm` parameter to mark an argument for (§9)");
});

test("a constructor written without parentheses is shown applied as it would be written", () => {
  says(`${nat}print ⟦Zero⟧;\n`, "`Zero` is a value constructor, which is not a value: it is applied, as in `Zero()`");
  says(`${nat}print ⟦Succ⟧;\n`, "`Succ` is a value constructor, which is not a value: it is applied, as in `Succ(...)`");
  says(`${nat}print ⟦Nat⟧;\n`, "`Nat` is a type constructor, which is not a value: it is applied, as in `Nat()`");
});

test("a qed against a type goal names the goal's proof", () => {
  says(`${nat}goal Nat();\nqed ⟦Nat()⟧;\n`, "the goal's proof must have type `Nat()`, and this has type `Type()`");
});

test("phase 2 syntax in a phase 1 program says so", () => {
  says(`${nat}print Succ(⟦_⟧);\n`,
    "`_` stands for an erased argument only from phase 2 on (§16), and this program is checked under phase 1");
  says(`${nat}fn f(⟦erased⟧ n : Nat()) -> (r : Nat()) { n }\n`,
    "`erased` is a multiplicity, which phase 2 adds (§16), and this program is checked under phase 1");
  says(`${nat}let ⟦many⟧ x = Zero();\n`,
    "`many` is a multiplicity, which phase 2 adds (§16), and this program is checked under phase 1");
});

test("pattern mistakes in a match are named", () => {
  const branches = (b: string) => `${nat}fn f(n : Nat()) -> (r : Nat()) {\n  match n : (r : Nat()) {\n${b}  }\n}\n`;
  says(branches("    Zero() => Zero();\n    Succ(Succ⟦(⟧m)) => m;\n"),
    "a pattern does not nest: it names each field of one value constructor, with a name or `_` (§10)");
  says(branches("    Zero() => Zero();\n    ⟦_⟧ => Zero();\n"),
    "a branch is for one value constructor, written as a pattern such as `C(x, _)`; there is no catch-all branch (§10)");
  says(branches("    ⟦Zero⟧ => Zero();\n    Succ(m) => m;\n"),
    "a pattern is written with its parentheses, even with no fields, as in `Zero()` (§1, §10)");
});

test("comptime on a let that is not a pattern let", () => {
  says(`${nat}⟦comptime⟧ let x = Zero();\n`,
    "`comptime` is written only on a pattern `let`, as in `comptime let C(x) = e;` (§11)");
});

test("returns and binders say how they are written", () => {
  says(`${nat}fn f(n : Nat()) -> ⟦Nat⟧() { n }\n`, "a function's returns are a telescope, as in `-> (r : Nat())` (§8)");
  const binder = "expected `:` or `is`, found `(`: a binder is written `name : T` or `name is e` (§1)";
  says(`${nat}fn f(n : Nat()) -> (Nat⟦(⟧)) { n }\n`, binder);
  says(`${nat}let x = sorry(Nat⟦(⟧));\n`, binder);
});

test("a block's final expression: no ; after it, and none missing", () => {
  says(`${nat}fn f(n : Nat()) -> (r : Nat()) { n⟦;⟧ }\n`, "a block ends with its final expression, which takes no `;` (§8)");
  says(`${nat}fn f(n : Nat()) -> (r : Nat()) { let m = n; ⟦}⟧\n`,
    "a block ends with a final expression, after its statements (§8)");
});

test("lexical messages write the text as code", () => {
  says("let x = ⟦2x⟧;\n", "`2x` is not a name: a name starts with a letter (§1)");
  says("let x = ⟦3⟧;\n", "`3` is not a name, and Pledge has no literals (§15)");
});
