import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { example } from "../examples.ts";
import { pages } from "../tutorial/pages.ts";

const html = (file: string): string => readFileSync(new URL(`../../web/${file}`, import.meta.url), "utf8");

const decoded = (text: string): string => text.replace(/&(lt|gt|quot|#39|amp);/g, (_, e: string) =>
  ({ lt: "<", gt: ">", quot: "\"", "#39": "'", amp: "&" })[e]!);

test("the front page's noscript block shows the example program the editor starts with", () => {
  const pre = /<noscript>[^]*<pre>([^]*)<\/pre>[^]*<\/noscript>/.exec(html("index.html"));
  assert.ok(pre);
  assert.equal(decoded(pre[1]!), example);
});

test("both pages have a description and a noscript block with content", () => {
  for (const file of ["index.html", "tutorial.html"]) {
    const page = html(file);
    assert.match(page, /<meta name="description" content="[^"]+">/, file);
    const noscript = /<noscript>([^]*)<\/noscript>/.exec(page);
    assert.ok(noscript && noscript[1]!.replace(/<[^>]*>/g, "").trim(), file);
  }
});

test("the tutorial's noscript block links each section, in order, to a source file that exists", () => {
  const links = [...html("tutorial.html").matchAll(/src\/tutorial\/(\w+\.ts)">([^<]*)</g)];
  assert.deepEqual(links.map(l => l[2]!.replace(/\s+/g, " ")), [...new Set(pages.map(p => p.section))]);
  for (const [, file] of links) readFileSync(new URL(`../tutorial/${file}`, import.meta.url));
});
