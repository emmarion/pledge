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
