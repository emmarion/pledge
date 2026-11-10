import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../src/check.ts";
import type { PositionInfo } from "../src/api.ts";
import { verdicts } from "./helpers.ts";
import { pages } from "../src/tutorial/pages.ts";

export const program = (boxes: string[], learner: string): string => [...boxes, learner].join("\n");
export const page = (slug: string) => pages.find(p => p.slug === slug)!;
export const run = (slug: string, learner: string) => {
  const p = page(slug);
  const source = program(p.boxes, learner);
  return { source, r: check(source, p.phase) };
};

export const errorAt = (slug: string, learner: string) => {
  const { source, r } = run(slug, learner);
  return { at: r.error ? source.slice(r.error.span.start, r.error.span.end) : null, message: r.error?.message() ?? "" };
};
export const expected = (info: PositionInfo) =>
  info.expected.entries?.map(e => `${e.name} : ${e.type?.text}${e.rule ? ` is ${e.rule.text}` : ""}`);
export const printsOf = (slug: string) => run(slug, page(slug).solution).r.prints.map(p => p.value);

export const infoAt = (slug: string, learner: string, marker: string, nth = 0) => {
  const { source, r } = run(slug, learner);
  let at = source.length - learner.length + learner.indexOf("\n");
  for (let i = 0; i <= nth; i++) at = source.indexOf(marker, at + 1);
  assert.ok(at >= 0, marker);
  return { r, info: r.infoAt(at) };
};

export const expectedAt = (slug: string, learner: string, marker: string, nth = 0): string =>
  infoAt(slug, learner, marker, nth).info.expected.entries!.map(e => `${e.name} : ${e.type!.text}`).join(", ");

export const gapsTest = (gaps: [slug: string, gaps: string[], qedChecks?: boolean | null][]): void => {
  const title = "the starting text checks with a sorry(_) in each gap the prose describes";
  for (const [slug, gap, qedChecks = true] of gaps) test(`${slug}: ${title}`, () => {
    const { initial } = page(slug);
    const { r } = run(slug, initial);
    assert.equal(r.error, null);
    assert.deepEqual(verdicts(r), [true, qedChecks, false]);
    assert.deepEqual(gap.map((_, i) => expectedAt(slug, initial, "sorry(_)", i)), gap);
  });
};
