import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { pages } from "./pages.ts";

const program = (boxes: string[], learner: string): string => [...boxes, learner].join("\n");

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
      assert.equal(r.goalProved, !sorry);
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
