import { h, type Child } from "./dom.ts";

const repo = "https://github.com/emmarion/pledge/blob/main/";

export const sections = [
  "1-syntax", "2-names", "3-skeleton-terms-and-types", "4-first-class-values", "5-data-types", "6-is",
  "7-what-the-checker-knows", "8-functions", "9-termination", "10-matching", "11-compile-time",
  "12-sorry-print-goal-and-qed", "13-seeing-what-the-checker-sees", "14-implementation", "15-not-in-phase-1",
  "16-later-phases", "17-review-status", "18-keywords", "19-grammar",
];

export const cited = /(§\d+|\b(?:DESIGN|SOUNDNESS)\.md)/;

export const citationUrl = (citation: string): string | null => {
  if (!citation.startsWith("§")) return repo + citation;
  const anchor = sections[Number(citation.slice(1)) - 1];
  return anchor === undefined ? null : `${repo}DESIGN.md#${anchor}`;
};

export const linked = (text: string): Child => text.split(cited).map((part, i) => {
  const href = i % 2 ? citationUrl(part) : null;
  return href ? h("a", { href, target: "_blank", rel: "noopener" }, part) : part;
});

export const marked = (text: string): Child => text.split(/(`[^`]*`|\*(?:[^*`]|`[^`]*`)+\*)/).map((part, i) => {
  const inner = part.slice(1, -1);
  return !(i % 2) ? linked(part) : part[0] === "`" ? h("code", {}, inner) : h("dfn", {}, marked(inner));
});
