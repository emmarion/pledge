import type { Phase, Span } from "./syntax.ts";

export interface Diagnostic { span: Span; message: () => string; derivation?: () => Rendered[] }

export type Ref = { span: Span; entry: EntryId } | { span: Span; declared: Span } | { span: Span; erased: true };
export interface Rendered { text: string; refs: Ref[] }

export type EntryId = number;

export interface Canonical { term: Rendered; rewrites: () => Rewrite[] }

export interface EntryInfo {
  id: EntryId;
  names: string[];
  origin: { kind: string; span: Span };
  marker: string;
  type: Rendered;
  rule: Rendered | null;
  ruleAt: Span | null;
  typeAt: Span;
  canonical: { type: Canonical; rule: Canonical | null };
  erased: boolean;
  tainted: string[];
}

export interface ExpectedEntry {
  name: string | null;
  type: Rendered | null;
  rule: Rendered | null;
  canonical: { type: Canonical | null; rule: Canonical | null };
  undetermined: boolean;
  erased: boolean;
}

export interface ExpectedInfo {
  entries: ExpectedEntry[] | null;
  params?: ExpectedEntry[];
}

export interface TerminationInfo {
  fn: string;
  subtermParams: string[];
  group: string[];
}

export interface RefutationInfo {
  ctor: string;
  kind: "refuted" | "absurd";
  derivation: () => Rendered[];
}

export interface GlobalInfo {
  kind: "fn" | "type";
  name: string;
  at: Span | null;
  signature: Rendered;
  ctors?: { name: string; at: Span | null; signature: Rendered }[];
}

export interface PositionInfo {
  expected: ExpectedInfo;
  termination: TerminationInfo | null;
  scope: EntryInfo[];
  globalEntries: EntryInfo[];
  topLevel: boolean;
  taintedBy: Span | null;
  refutations: RefutationInfo[] | null;
  globals: GlobalInfo[];
}

export type NameInfo =
  | { kind: "entry"; entry: EntryInfo }
  | { kind: "fn" | "type" | "ctor"; name: string; signature: Rendered };

export interface Rewrite { from: Rendered; to: Rendered; by: EntryId; at: Span; rule: Rendered; how: () => Rendered[] }

export type Explained = { span: Span } & ({ canonical: Rendered; rewrites: Rewrite[] } | { stands: ExpectedEntry[] });

export interface CheckResult {
  phase: Phase;
  error: Diagnostic | null;
  containsSorry: boolean;
  qed: "none" | "unreached" | "fails" | "checks";
  goalProved: boolean | null;
  prints: { span: Span; value: string }[];
  erased: Span[];
  inspects: { span: Span; info: PositionInfo }[];
  infoAt(offset: number): PositionInfo;
  nameAt(offset: number): NameInfo | null;

  explainAt(offset: number): Explained | null;

  evalAt(offset: number, text: string):
    | { type: Rendered; canonicalType: Rendered; rule: Rendered | null; canonicalRule: Rendered | null }
    | { error: Diagnostic };
}

export type Check = (source: string, phase: Phase, where?: (offset: number) => string) => CheckResult;
