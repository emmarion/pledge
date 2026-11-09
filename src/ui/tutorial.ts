import { disclaimer, pages } from "../tutorial/pages.ts";
import { cited, citationUrl } from "../tutorial/links.ts";
import { h, type Child } from "./dom.ts";
import { Workspace } from "./workspace.ts";

const slug = new URLSearchParams(location.search).get("page");
const index = Math.max(0, pages.findIndex(p => p.slug === slug));
const page = pages[index]!;
const href = (i: number): string => `?page=${encodeURIComponent(pages[i]!.slug)}`;

const linked = (text: string): Child => text.split(cited).map((part, i) => {
  const href = i % 2 ? citationUrl(part) : null;
  return href ? h("a", { href, target: "_blank", rel: "noopener" }, part) : part;
});

const prose = page.prose.split(/\n\s*\n/).map(paragraph =>
  h("p", {}, paragraph.split("`").map((part, i) => i % 2 ? h("code", {}, part) : linked(part))));

const fixed = [...page.boxes.keys()];
const workspace = new Workspace(
  [...page.boxes.map(text => ({ text, key: null })), { text: page.initial, key: `page:${page.slug}`, holdsQed: page.requireQed }, { text: page.solution, key: null }],
  () => page.phase,
  [{ label: "your box", boxes: [...fixed, fixed.length] }, { label: "the solution", boxes: [...fixed, fixed.length + 1] }]);

document.title = `${page.title} — Pledge tutorial`;
workspace.mount(
  [h("h1", {}, h("a", { href: "index.html" }, "Pledge"), " tutorial"), h("span", { class: "muted" }, `Phase ${page.phase}`)],
  "Reset your box",
  [h("details", { class: "disclaimer" }, h("summary", {}, "Disclaimer"), h("p", {}, linked(disclaimer))), h("h2", {}, page.title), prose],
  [h("details", { class: "solution" }, h("summary", {}, "Show a solution"), workspace.editors.at(-1)!.root),
  h("p", { class: "pager" },
    index > 0 && h("a", { href: href(index - 1) }, `← ${pages[index - 1]!.title}`),
    index + 1 < pages.length && h("a", { href: href(index + 1), class: "next" }, `${pages[index + 1]!.title} →`))],
  h("nav", { class: "toc", "aria-label": "Pages" }, h("ol", {}, pages.map((p, i) =>
    h("li", {}, h("a", { href: href(i), "aria-current": i === index && "page" }, p.title))))));
