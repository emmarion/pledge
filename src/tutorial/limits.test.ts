import { test } from "node:test";
import assert from "node:assert/strict";
import { entriesOf, file, listed, verdicts } from "../../tests/helpers.ts";
import { page, run } from "../../tests/tutorial.ts";
import { agda } from "./limits.ts";

test("comptime: n is known only by its type, so only the run proves Even(n)", () => {
  const { r } = run("comptime", page("comptime").solution);
  assert.deepEqual(verdicts(r), [false, true, true]);
  assert.equal(r.prints[0]?.value, `${"Succ(".repeat(100)}Zero()${")".repeat(100)}`);
  assert.match(run("comptime", page("comptime").initial).r.error?.message() ?? "", /`None` is not refuted/);
  assert.match(run("comptime", "qed EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()));\n").r.error?.message() ?? "", /type `Even\(n\)`/);
  const fallback = run("comptime", "let p = match decideEven(n) : (p : Even(n)) {\n  None(_) => sorry(_);\n  Some(_, q) => q;\n};\nqed p;\n").r;
  assert.deepEqual(verdicts(fallback), [true, true, false]);
});

test("soundness: marking n subterm does not help loop, a match with no branches is rejected, and sorry leaves the goal unproved", () => {
  assert.match(run("soundness", page("soundness").initial.replace("loop(n)", "match n : _ {}")).r.error?.message() ?? "", /no branch for `Zero`, `Succ`/);
  const marked = page("soundness").initial.replace("loop(n : Nat())", "loop(subterm n : Nat())").replace("loop(n)", "loop(subterm n)");
  assert.match(run("soundness", marked).r.error?.message() ?? "", /not a strict subterm/);
  assert.deepEqual(verdicts(run("soundness", page("soundness").solution).r), [true, true, false]);
});

test("beyond: the start fails at qed p, with p's type ending in r, while print shows four", () => {
  const { source, r } = run("beyond", page("beyond").initial);
  assert.equal(r.error?.span.start, source.indexOf("qed p;") + 4);
  assert.equal(r.qed, "fails");
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Succ(Succ(Succ(Zero()))))"]);
  assert.ok(entriesOf(r.infoAt(source.indexOf("qed p;"))).includes("p : Plus(Succ(Succ(Zero())), Succ(Succ(Zero())), r)"));
});

test("beyond: each pattern let refutes the other value constructor and moves r one step towards four", () => {
  const { source, r } = run("beyond", page("beyond").solution);
  assert.deepEqual(verdicts(r), [false, true, true]);
  const lets = [...source.matchAll(/^let Plus\w+/gm)].map(m => m.index! + 4);
  assert.deepEqual(lets.map(at => r.infoAt(at).refutations?.map(x => x.ctor)), [["PlusZero"], ["PlusZero"], ["PlusSucc"]]);
  const rRule = (at: number) => listed(r.infoAt(at)).find(e => e.names.includes("r"))?.canonical.rule?.term.text;
  assert.deepEqual([...lets.slice(1), source.indexOf("qed p;")].map(rRule),
    ["Succ(r1)", "Succ(Succ(r2))", "Succ(Succ(Succ(Succ(Zero()))))"]);
});

test("beyond: every line of the page's Agda occurs in tests/Beyond.agda", () => {
  const lines = new Set(file("Beyond.agda").split("\n"));
  for (const line of agda.split("\n")) assert.ok(lines.has(line), line);
  assert.ok(page("beyond").prose.includes(`\`\`\`\n${agda}\n\`\`\``));
});
