import { disclaimer, pages } from "../tutorial/pages.ts";
import { glossary } from "../tutorial/glossary.ts";
import { h } from "./dom.ts";
import { linked, marked } from "./links.ts";
import { Workspace } from "./workspace.ts";

const slug = new URLSearchParams(location.search).get("page");
const index = Math.max(0, pages.findIndex(p => p.slug === slug));
const page = pages[index]!;
const href = (i: number): string => `?page=${encodeURIComponent(pages[i]!.slug)}`;

const paragraphs = (text: string) => text.split(/\n\s*\n/).map(paragraph => /^```\n[^]*\n```$/.test(paragraph)
  ? h("pre", { class: "foreign" }, paragraph.slice(4, -4)) : h("p", {}, marked(paragraph)));

const link = (i: number) => h("a", { href: href(i) }, pages[i]!.title);

const fixed = [...page.boxes.keys()];
const key = `page:${page.slug}${page.revision ? `:${page.revision}` : ""}`;
const workspace = new Workspace(
  [...page.boxes.map(text => ({ text, key: null })), { text: page.initial, key, holdsQed: page.requireQed },
    { text: page.solution, key: null }],
  () => page.phase,
  [{ label: "your box", boxes: [...fixed, fixed.length] }, { label: "the solution",
    boxes: [...fixed, fixed.length + 1] }]);

const next = pages[index + 1];
const resume = next?.optional && !page.optional ? pages.findIndex((p, i) => i > index && !p.optional) : -1;
const toc = h("details", { class: "toc" }, h("summary", {}, "Pages"),
  h("nav", { "aria-label": "Pages" }, [...new Set(pages.map(p => p.section))].map(section =>
    [h("h2", {}, section, pages.find(p => p.section === section)!.optional && h("span", { class: "note" }, "optional")),
      h("ol", {}, pages.map((p, i) => p.section === section && h("li", {},
        h("a", { href: href(i), "aria-current": i === index && "page" }, p.title,
          p.phase > 1 && h("span", { class: "tag" }, `phase ${p.phase}`)))))])));
document.title = `${page.title} — Pledge tutorial`;
workspace.mount(
  [h("h1", {}, h("a", { href: "index.html" }, "Pledge"), " tutorial"),
    h("span", { class: "muted" }, `Phase ${page.phase}`)],
  { label: "Reset your box", question: "Replace your text with the starting text? This cannot be undone." },
  [h("div", { class: "about" },
    h("details", { class: "disclaimer" }, h("summary", {}, "Disclaimer"), h("p", {}, linked(disclaimer))),
    h("details", { class: "glossary" }, h("summary", {}, "Glossary"), h("dl", {}, glossary.map(g => [
      h("dt", {}, marked(g.term)),
      h("dd", {}, marked(g.means), " ", link(pages.findIndex(p => p.slug === g.at)))])))),
  h("p", { class: "muted" }, page.section), h("h2", {}, page.title), paragraphs(page.prose),
  h("section", { class: "task" }, h("h3", {}, "Task"), paragraphs(page.task)),
  h("p", { class: "muted refs" }, linked(`In DESIGN.md: ${page.refs}.`))],
  [h("details", { class: "solution" }, h("summary", {}, "Show a solution"), workspace.editors.at(-1)!.root),
  h("p", { class: "pager" },
    index > 0 && h("a", { href: href(index - 1) }, `← ${pages[index - 1]!.title}`),
    next && h("span", { class: "next" },
      resume >= 0 && [h("a", { href: href(resume) }, `Skip to ${pages[resume]!.title}`), " · "],
      h("a", { href: href(index + 1) },
        `${next.optional && !page.optional ? next.appendix ? "Appendix: " : "Optional: " : ""}${next.title} →`)))],
  toc);

const wide = matchMedia("(min-width: 1440px)");
const sync = (): void => { toc.open = wide.matches; };
wide.addEventListener("change", sync);
sync();
