import { check } from "../src/check.ts";
import { pages } from "../src/tutorial/pages.ts";

export const program = (boxes: string[], learner: string): string => [...boxes, learner].join("\n");
export const page = (slug: string) => pages.find(p => p.slug === slug)!;
export const run = (slug: string, learner: string) => {
  const p = page(slug);
  const source = program(p.boxes, learner);
  return { source, r: check(source, p.phase) };
};
