import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { readFileSync } from "node:fs";
import { disclaimer, pages } from "./pages.ts";
import { cited, citationUrl, sections } from "./links.ts";

const program = (boxes: string[], learner: string): string => [...boxes, learner].join("\n");

test("section links match DESIGN.md's headings, and every citation in the prose has a link", () => {
  const headings = [...readFileSync(new URL("../../DESIGN.md", import.meta.url), "utf8").matchAll(/^## (.*)$/gm)]
    .map(m => m[1]!.toLowerCase().replace(/[^a-z0-9 -]/g, "").replaceAll(" ", "-"));
  assert.deepEqual(sections, headings);
  for (const text of [disclaimer, ...pages.map(p => p.prose)])
    for (const part of text.split(cited).filter((_, i) => i % 2)) assert.notEqual(citationUrl(part), null, part);
});

test("slugs are unique", () => {
  assert.equal(new Set(pages.map(p => p.slug)).size, pages.length);
});

for (const page of pages) {
  test(`${page.slug}: the starting text checks or fails readably`, () => {
    const r = check(program(page.boxes, page.initial), page.phase);
    if (r.error) assert.doesNotMatch(r.error.message(), /internal|undefined|\[object/i);
  });

  test(`${page.slug}: the solution checks`, () => {
    const source = program(page.boxes, page.solution);
    const r = check(source, page.phase);
    assert.equal(r.error && r.error.message(), null);
    const sorry = /\bsorry\(/.test(source);
    assert.equal(r.containsSorry, sorry);
    if (page.requireQed) {
      assert.match(page.solution, /\bqed\b/);
      assert.equal(r.goalProved, !/\bsorry\(/.test(page.solution));
    }
  });
}

test("erased-positions: both fixes check, and only keeping n lets print show the length", () => {
  const page = pages.find(p => p.slug === "erased-positions")!;
  const printed = (learner: string) => check(program(page.boxes, `${learner}print len(Nat(), Succ(Zero()), v);\n`), page.phase);
  const keepN = page.solution.replace("erased m is n", "m is n").replace("erased n : Nat(), v", "n : Nat(), v");
  assert.equal(check(program(page.boxes, keepN), page.phase).error, null);
  assert.deepEqual(printed(keepN).prints.map(p => p.value).at(-1), "Succ(Zero())");
  assert.match(printed(page.solution).error?.message() ?? "", /erased/);
});

test("holes: a block's final expression takes part in solving a `_`", () => {
  const page = pages.find(p => p.slug === "holes")!;
  const r = check(program(page.boxes, `${page.solution}print vhead(_, _, { v });\n`), page.phase);
  assert.equal(r.error && r.error.message(), null);
  assert.equal(r.prints.at(-1)?.value, "Zero()");
});

test("times-distrib: a binder the later clauses of its `let` refer to needs a type", () => {
  const page = pages.find(p => p.slug === "times-distrib")!;
  const r = check(program(page.boxes.map(b => b.replace("let (yxz : Nat(),", "let (yxz,")), page.solution), page.phase);
  assert.match(r.error?.message() ?? "", /`yxz` has no type here/);
});

const page = (slug: string) => pages.find(p => p.slug === slug)!;
const run = (slug: string, learner: string) => { const p = page(slug); const source = program(p.boxes, learner); return { source, r: check(source, p.phase) }; };
const verdicts = (r: ReturnType<typeof check>) => [r.containsSorry, r.qedChecks, r.goalProved];
const scopeAt = (r: ReturnType<typeof check>, offset: number) => r.infoAt(offset).scope.map(e => `${e.names.join(",") || `?${e.origin.kind}`} : ${e.type.text}${e.rule ? ` is ${e.rule.text}` : ""}`);

test("fine points: the new pages are the last ones, phase 1 unless they need phase 2", () => {
  const slugs = ["tuple-let-telescope", "facts-escape", "tainted-pattern-let", "hole-through-block", "hole-taint", "goal-comparison", "absurd-branches"];
  assert.deepEqual(pages.slice(-slugs.length).map(p => [p.slug, p.phase]), slugs.map(s => [s, ["hole-through-block", "hole-taint", "absurd-branches"].includes(s) ? 2 : 1]));
});

test("every program line fits in 72 columns", () => {
  for (const p of pages) for (const line of [...p.boxes, p.initial, p.solution].join("\n").split("\n")) assert.ok(line.length <= 72, `${p.slug}: ${line}`);
});

test("comptime: n is known only by its type, so only the run proves Even(n)", () => {
  const { r } = run("comptime", page("comptime").solution);
  assert.deepEqual(verdicts(r), [false, true, true]);
  assert.equal(r.prints[0]?.value, `${"Succ(".repeat(100)}Zero()${")".repeat(100)}`);
  assert.match(run("comptime", page("comptime").initial).r.error?.message() ?? "", /None is not refuted/);
  assert.match(run("comptime", "qed EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()));\n").r.error?.message() ?? "", /type Even\(n\)/);
  const fallback = run("comptime", "let p = match decideEven(n) : (p : Even(n)) {\n  None(_) => sorry(_);\n  Some(_, q) => q;\n};\nqed p;\n").r;
  assert.deepEqual(verdicts(fallback), [true, true, false]);
});

test("iszero: the Succ branch cannot be filled with Refl", () => {
  const junk = page("iszero").solution.replace("match p : _ {}", "Refl(Nat(), n)");
  assert.match(run("iszero", junk).r.error?.message() ?? "", /Eq\(Nat\(\), Succ\(m\), Zero\(\)\)/);
});

test("tuple-let-telescope: Expected lists both binders, and dropping m's type is an error at the reference", () => {
  const { source, r } = run("tuple-let-telescope", page("tuple-let-telescope").solution);
  assert.deepEqual(r.infoAt(source.indexOf("pair(x)")).expected.entries?.map(e => `${e.name} : ${e.type?.text}`), ["m : Nat()", "v : Vec(Nat(), Succ(m))"]);
  assert.ok(scopeAt(r, source.indexOf("print v")).includes("v : Vec(Nat(), Succ(m))"));
  const dropped = run("tuple-let-telescope", page("tuple-let-telescope").solution.replace("m : Nat(),", "m,"));
  assert.match(dropped.r.error?.message() ?? "", /`m` has no type here/);
  assert.equal(dropped.r.error?.span.start, dropped.source.indexOf("Succ(m)))") + 5);
});

test("facts-escape: after the block, v's rule and the anonymous tail remain, and the goal needs them", () => {
  const { source, r } = run("facts-escape", page("facts-escape").solution);
  const after = scopeAt(r, source.indexOf("inspect;"));
  assert.ok(after.some(e => /^v : .* is VCons\(Nat\(\), n, h, \?VCons\.rest@/.test(e)), after.join("; "));
  assert.ok(after.includes("?VCons.rest : Vec(Nat(), n)"), after.join("; "));
  assert.ok(!after.some(e => /^(hd|tl)\b/.test(e)));
  assert.match(run("facts-escape", `let k = tl;\n${page("facts-escape").solution}`).r.error?.message() ?? "", /tl is not in scope/);
  const p = page("facts-escape");
  const noEscape = check(program(p.boxes.map(b => b.replace("{ let VCons(_, _, hd, tl) = v; hd }", "Zero()")), p.solution), p.phase);
  assert.equal(noEscape.goalProved, false);
});

test("tainted-pattern-let: every statement checks, yet print shows sorry and the goal is not proved; in a branch only the match is tainted", () => {
  const { r } = run("tainted-pattern-let", page("tainted-pattern-let").initial);
  assert.equal(r.error, null);
  assert.deepEqual(verdicts(r), [true, true, false]);
  assert.deepEqual(r.prints.map(p => p.value), ["sorry", "Zero()", "sorry"]);
  assert.deepEqual(run("tainted-pattern-let", page("tainted-pattern-let").solution).r.prints.map(p => p.value), ["sorry", "Zero()", "Zero()"]);
});

test("hole-through-block: the _s are solved through the block's final expression", () => {
  const { source, r } = run("hole-through-block", page("hole-through-block").solution);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())", "Succ(Zero())"]);
  const at = source.indexOf("vhead(_, _, { let") + 6;
  assert.deepEqual([r.explainAt(at)?.canonical.text, r.explainAt(at + 3)?.canonical.text], ["Nat()", "Zero()"]);
  assert.deepEqual(r.infoAt(at).expected.entries?.map(e => [e.name, e.erased]), [["A", true]]);
});

test("hole-taint: a _ solved to a sorry result taints the call; with Nat() the goal is proved", () => {
  const { source, r } = run("hole-taint", page("hole-taint").initial);
  assert.deepEqual([verdicts(r), r.prints.map(p => p.value)], [[true, true, false], ["sorry"]]);
  assert.equal(r.explainAt(source.indexOf("VNil(_));") + 5)?.canonical.text, "A");
  const clean = run("hole-taint", page("hole-taint").solution).r;
  assert.deepEqual([verdicts(clean), clean.prints.map(p => p.value)], [[false, true, true], ["Zero()"]]);
});

test("goal-comparison: an earlier is clause is not in force, so the starting text names return 1; changing the goal also works", () => {
  const { r } = run("goal-comparison", page("goal-comparison").initial);
  assert.match(r.error?.message() ?? "", /succEq's return 1 is `e : Eq\(Nat\(\), Succ\(a\), b\)`, and the goal's is `e : Eq\(Nat\(\), b, Succ\(a\)\)`/);
  assert.deepEqual(verdicts(r), [false, false, false]);
  const goalChanged = run("goal-comparison", page("goal-comparison").initial.replace("Eq(Nat(), b, Succ(a))", "Eq(Nat(), Succ(a), b)")).r;
  assert.deepEqual(verdicts(goalChanged), [false, true, true]);
});

test("absurd-branches: Succ is absurd, IsZeroHere refuted, and print runs the live branch", () => {
  const { source, r } = run("absurd-branches", page("absurd-branches").solution);
  assert.deepEqual(r.prints.map(p => p.value), ["Zero()"]);
  assert.deepEqual(r.infoAt(source.indexOf("match erased") + 2).refutations?.map(x => [x.ctor, x.kind]), [["Succ", "absurd"]]);
  assert.deepEqual(r.infoAt(source.indexOf("match p") + 2).refutations?.map(x => [x.ctor, x.kind]), [["IsZeroHere", "refuted"]]);
  assert.match(run("absurd-branches", page("absurd-branches").initial).r.error?.message() ?? "", /no branch for Succ/);
});
