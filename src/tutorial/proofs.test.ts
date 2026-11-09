import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { scopeOf, verdicts } from "../../tests/helpers.ts";
import { page, program, run } from "../../tests/tutorial.ts";

const infoAt = (slug: string, learner: string, marker: string, nth = 0) => {
  const { source, r } = run(slug, learner);
  let at = source.length - learner.length + learner.indexOf("\n");
  for (let i = 0; i <= nth; i++) at = source.indexOf(marker, at + 1);
  assert.ok(at >= 0, marker);
  return { r, info: r.infoAt(at) };
};

const expectedAt = (slug: string, learner: string, marker: string, nth = 0): string =>
  infoAt(slug, learner, marker, nth).info.expected.entries!.map(e => `${e.name} : ${e.type!.text}`).join(", ");

const gaps: [string, string[]][] = [
  ["plus-zero", ["e : Eq(Nat(), Zero(), Zero())", "e : Eq(Nat(), Succ(r1), Succ(m))"]],
  ["plus-succ", ["q : Plus(Zero(), Succ(n), Succ(n))", "q : Plus(Succ(m1), Succ(n), Succ(Succ(r1)))"]],
  ["plus-comm", ["q : Plus(n, Zero(), n)", "q : Plus(n, Succ(m1), Succ(r1))"]],
  ["plus-assoc", ["bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(Zero(), bc, r)"]],
  ["times-distrib", ["ab : Nat(), ac : Nat(), t1 : Times(Zero(), b, ab), t2 : Times(Zero(), c, ac), q : Plus(ab, ac, Zero())"]],
];

for (const [slug, expected] of gaps) test(`${slug}: the starting text checks with a sorry(_) in each gap the prose describes`, () => {
  const { initial } = page(slug);
  const { r } = run(slug, initial);
  assert.equal(r.error, null);
  assert.deepEqual(verdicts(r), [true, slug === "plus-zero" ? null : true, false]);
  assert.deepEqual(expected.map((_, i) => expectedAt(slug, initial, "sorry(_)", i)), expected);
});

test("plus-zero: in the Refl branch r1 is m, and the branch is tainted by the call while a sorry is left", () => {
  const learner = page("plus-zero").solution.replace("Refl(_, _) => Refl(Nat(), r)", "Refl(_, _) => sorry(_)");
  const { info } = infoAt("plus-zero", `--\n${learner}`, "sorry(_)");
  assert.equal(expectedAt("plus-zero", `--\n${learner}`, "sorry(_)"), "e : Eq(Nat(), Succ(m), Succ(m))");
  assert.ok(scopeOf(info).includes("r1 : Nat() is m"));
  assert.notEqual(info.taintedBy, null);
});

test("plus-zero: a type contains no function call", () => {
  const learner = "fn bad(n : Nat()) -> (e : Eq(Nat(), plus(n, Zero()), n)) {\n  sorry(_)\n}\n";
  assert.match(run("plus-zero", learner).r.error?.message() ?? "", /a type contains no function call/);
});

test("sorry: sorry(_) takes the let's type, taints p, and an explicit telescope works at an argument", () => {
  const { initial } = page("sorry");
  const { r } = run("sorry", initial);
  assert.deepEqual(verdicts(r), [true, true, false]);
  assert.deepEqual(r.prints.map(p => p.value), ["sorry"]);
  assert.equal(expectedAt("sorry", initial, "sorry(_)"), "p : Even(Succ(Succ(Succ(Succ(Zero())))))");
  assert.deepEqual(infoAt("sorry", initial, "print").info.scope.find(e => e.names.includes("p"))?.tainted, ["p"]);
  const step = initial.replace("sorry(_);", "EvenSucc(three, sorry(q : Odd(three)));");
  assert.equal(run("sorry", step).r.error, null);
  assert.equal(expectedAt("sorry", step, "sorry(q"), "p : Odd(Succ(Succ(Succ(Zero()))))");
});

test("equality: two in the goal canonicalizes to Succ(Succ(Zero())) in two rewrites", () => {
  const p = page("equality");
  const source = program(p.boxes, p.initial);
  const explained = check(source, p.phase).explainAt(source.indexOf("two, Succ(Succ"));
  assert.equal(explained?.canonical.text, "Succ(Succ(Zero()))");
  assert.equal(explained?.rewrites.length, 2);
});

test("soundness: marking n subterm does not help loop, and sorry leaves the goal unproved", () => {
  const marked = page("soundness").initial.replace("loop(n : Nat())", "loop(subterm n : Nat())").replace("loop(n)", "loop(subterm n)");
  assert.match(run("soundness", marked).r.error?.message() ?? "", /not a strict subterm/);
  assert.deepEqual(verdicts(run("soundness", page("soundness").solution).r), [true, true, false]);
});

test("times-distrib: a binder the later clauses of its `let` refer to needs a type", () => {
  const p = page("times-distrib");
  const r = check(program(p.boxes.map(b => b.replace("let (yxz : Nat(),", "let (yxz,")), p.solution), p.phase);
  assert.match(r.error?.message() ?? "", /`yxz` has no type here/);
});

test("comptime: n is known only by its type, so only the run proves Even(n)", () => {
  const { r } = run("comptime", page("comptime").solution);
  assert.deepEqual(verdicts(r), [false, true, true]);
  assert.equal(r.prints[0]?.value, `${"Succ(".repeat(100)}Zero()${")".repeat(100)}`);
  assert.match(run("comptime", page("comptime").initial).r.error?.message() ?? "", /`None` is not refuted/);
  assert.match(run("comptime", "qed EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()));\n").r.error?.message() ?? "", /type `Even\(n\)`/);
  const fallback = run("comptime", "let p = match decideEven(n) : (p : Even(n)) {\n  None(_) => sorry(_);\n  Some(_, q) => q;\n};\nqed p;\n").r;
  assert.deepEqual(verdicts(fallback), [true, true, false]);
});

test("iszero: the Succ branch cannot be filled with Refl", () => {
  const junk = page("iszero").solution.replace("match p : _ {}", "Refl(Nat(), n)");
  assert.match(run("iszero", junk).r.error?.message() ?? "", /Eq\(Nat\(\), Succ\(m\), Zero\(\)\)/);
});
