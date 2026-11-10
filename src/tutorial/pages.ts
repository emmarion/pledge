import type { Phase } from "../syntax.ts";
import { start } from "./start.ts";
import { dependent } from "./dependent.ts";
import { recursion } from "./recursion.ts";
import { evidence } from "./evidence.ts";
import { relation } from "./relation.ts";
import { arithmetic } from "./arithmetic.ts";
import { limits } from "./limits.ts";
import { erasure } from "./erasure.ts";
import { appendix } from "./appendix.ts";

export interface Page {
  section: string;
  optional: boolean;
  appendix: boolean;
  slug: string;
  title: string;
  phase: Phase;
  prose: string;
  task: string;
  refs: string;
  boxes: string[];
  initial: string;
  requireQed: boolean;
  solution: string;
  revision?: number;
}

export interface Section {
  title: string;
  optional?: boolean;
  appendix?: boolean;
  pages: Omit<Page, "section" | "optional" | "appendix">[];
}

export const disclaimer = "This tutorial was written by a Claude session, not by Pledge's owner, and may contain mistakes. DESIGN.md is the specification; where the two disagree, DESIGN.md is right and this tutorial is wrong. Each page ends with the DESIGN.md sections (§) its claims are based on. What the pages say about Pledge's soundness rests on SOUNDNESS.md, a written argument that no machine has checked. What they say about other languages, and their reasons for Pledge's rules, are the session's own. Where DESIGN.md is silent, the pages describe what this implementation does; ASSUMPTIONS.md lists those choices.";

const sections = [start, dependent, recursion, evidence, relation, arithmetic, limits, erasure, appendix];

export const pages: Page[] = sections.flatMap(({ title, optional = false, appendix = false, pages }) =>
  pages.map(p => ({ ...p, section: title, optional: optional || appendix, appendix })));
