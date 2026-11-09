import { test } from "node:test";
import assert from "node:assert/strict";
import { file, scopeOf, verdicts } from "../../tests/helpers.ts";
import { page, run } from "../../tests/tutorial.ts";
import { agda } from "./beyond.ts";

test("beyond: the start fails at qed p, with p's type ending in r, while print shows four", () => {
  const { source, r } = run("beyond", page("beyond").initial);
  assert.equal(r.error?.span.start, source.indexOf("qed p;") + 4);
  assert.equal(r.qed, "fails");
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Succ(Succ(Succ(Zero()))))"]);
  assert.ok(scopeOf(r.infoAt(source.indexOf("qed p;"))).includes("p : Plus(Succ(Succ(Zero())), Succ(Succ(Zero())), r)"));
});

test("beyond: each pattern let refutes the other value constructor and moves r one step towards four", () => {
  const { source, r } = run("beyond", page("beyond").solution);
  assert.deepEqual(verdicts(r), [false, true, true]);
  const lets = [...source.matchAll(/^let Plus\w+/gm)].map(m => m.index! + 4);
  assert.deepEqual(lets.map(at => r.infoAt(at).refutations?.map(x => x.ctor)), [["PlusZero"], ["PlusZero"], ["PlusSucc"]]);
  const rRule = (at: number) => r.infoAt(at).scope.find(e => e.names.includes("r"))?.rule?.text;
  assert.deepEqual([...lets.slice(1), source.indexOf("qed p;")].map(rRule),
    ["Succ(r1)", "Succ(Succ(r2))", "Succ(Succ(Succ(Succ(Zero()))))"]);
});

test("beyond: every line of the page's Agda occurs in tests/Beyond.agda", () => {
  const lines = new Set(file("Beyond.agda").split("\n"));
  for (const line of agda.split("\n")) assert.ok(lines.has(line), line);
  assert.ok(page("beyond").prose.includes(`\`\`\`\n${agda}\n\`\`\``));
});
