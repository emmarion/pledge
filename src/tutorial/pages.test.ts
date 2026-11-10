import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { readFileSync } from "node:fs";
import { disclaimer, pages } from "./pages.ts";
import { glossary } from "./glossary.ts";
import { cited, citationUrl, sections } from "../ui/links.ts";
import { program } from "../../tests/tutorial.ts";

test("section links match DESIGN.md's headings, and every citation in the pages and the glossary has a link", () => {
  const headings = [...readFileSync(new URL("../../DESIGN.md", import.meta.url), "utf8").matchAll(/^## (.*)$/gm)]
    .map(m => m[1]!.toLowerCase().replace(/[^a-z0-9 -]/g, "").replaceAll(" ", "-"));
  assert.deepEqual(sections, headings);
  for (const text of [disclaimer, ...pages.flatMap(p => [p.prose, p.task, p.refs]), ...glossary.flatMap(g => [g.term, g.means, g.elsewhere ?? ""])])
    for (const part of text.split(cited).filter((_, i) => i % 2)) assert.notEqual(citationUrl(part), null, part);
});

test("a page whose saved text from before its rewrite no longer checks keeps a revision", () => {
  assert.deepEqual(pages.filter(p => p.revision).map(p => [p.slug, p.revision]), [["functions", 2], ["mutual", 2]]);
});

test("slugs are unique", () => {
  assert.equal(new Set(pages.map(p => p.slug)).size, pages.length);
});

test("every page has a task and refs, and refs are sections in ascending order", () => {
  for (const p of pages) {
    assert.ok(p.task.trim(), p.slug);
    assert.match(p.refs, /^§\d+(, §\d+)*$/, p.slug);
    const refs = p.refs.split(", ").map(r => Number(r.slice(1)));
    assert.deepEqual(refs, [...new Set(refs)].sort((a, b) => a - b), p.slug);
  }
});

test("glossary terms are unique, and each is defined at a page", () => {
  assert.equal(new Set(glossary.map(g => g.term)).size, glossary.length);
  for (const g of glossary) assert.ok(pages.some(p => p.slug === g.at), `${g.term}: ${g.at}`);
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

test("appendix: its pages are the last ones, phase 1 unless they need phase 2", () => {
  const slugs = ["tuple-let-telescope", "facts-escape", "tainted-pattern-let", "hole-through-block", "hole-taint", "goal-comparison"];
  assert.deepEqual(pages.filter(p => p.appendix).map(p => p.slug), slugs);
  assert.deepEqual(pages.slice(-slugs.length).map(p => [p.slug, p.phase]), slugs.map(s => [s, ["hole-through-block", "hole-taint"].includes(s) ? 2 : 1]));
});

test("optional sections: the appendix and the arithmetic pages, with a page of the main path after the latter", () => {
  assert.deepEqual([...new Set(pages.filter(p => p.optional).map(p => p.section))], ["Arithmetic", "Appendix: fine points"]);
  assert.equal(pages.find((p, i) => !p.optional && pages[i - 1]?.optional)?.slug, "comptime");
});

test("a page named in another page's prose or task exists", () => {
  const titles = new Set(pages.map(p => p.title));
  for (const p of pages) for (const [, title] of `${p.prose} ${p.task}`.matchAll(/pages? "([^"]+)"/g))
    assert.ok(titles.has(title!), `${p.slug}: ${title}`);
});

test("every program line fits in 72 columns", () => {
  for (const p of pages) for (const line of [...p.boxes, p.initial, p.solution].join("\n").split("\n")) assert.ok(line.length <= 72, `${p.slug}: ${line}`);
});
