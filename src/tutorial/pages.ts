import type { Phase } from "../syntax.ts";
import { basics } from "./basics.ts";
import { proofs } from "./proofs.ts";
import { erasure } from "./erasure.ts";
import { appendix } from "./appendix.ts";

export interface Page {
  section: string;
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
}

export interface Section {
  title: string;
  appendix?: boolean;
  pages: Omit<Page, "section" | "appendix">[];
}

export const disclaimer = "This tutorial was written by a Claude session, not by Pledge's owner. DESIGN.md is the specification; where the two disagree, DESIGN.md is right and this tutorial is wrong. Each page ends with the DESIGN.md sections (§) its claims are based on.";

export const pages: Page[] = [basics, proofs, erasure, appendix].flatMap(s =>
  s.pages.map(p => ({ ...p, section: s.title, appendix: s.appendix ?? false })));
