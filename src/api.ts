
import type { Phase, Span } from "./syntax.ts";

export interface Diagnostic { span: Span; message: () => string }

export interface Rendered { text: string; refs: { span: Span; entry: EntryId }[] }

export type EntryId = number;

export interface EntryInfo {
  id: EntryId;
  names: string[];
  origin: { kind: string; span: Span };
  type: Rendered;
  rule: Rendered | null;
  erased: boolean;
  tainted: boolean;
}

export interface ExpectedEntry { name: string | null; type: Rendered | null; rule: Rendered | null; undetermined: boolean; erased: boolean }

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

export interface GlobalInfo { kind: "fn" | "type" | "binding"; name: string; signature: Rendered; ctors?: { name: string; signature: Rendered }[] }

export interface PositionInfo {
  expected: ExpectedInfo;
  termination: TerminationInfo | null;
  scope: EntryInfo[];
  refutations: RefutationInfo[] | null;
  globals: GlobalInfo[];
}

export interface Rewrite { from: Rendered; to: Rendered; by: EntryId; at: Span }

export interface CheckResult {
  phase: Phase;
  error: Diagnostic | null;
  containsSorry: boolean;
  qedChecks: boolean | null;
  goalProved: boolean | null;
  prints: { span: Span; value: string }[];
  inspects: { span: Span; info: PositionInfo }[];
  infoAt(offset: number): PositionInfo;

  explainAt(offset: number): { canonical: Rendered; rewrites: Rewrite[] } | null;

  evalAt(offset: number, text: string): { type: Rendered; canonicalType: Rendered; rule: Rendered | null; canonicalRule: Rendered | null } | { error: Diagnostic };
}

export type Check = (source: string, phase: Phase, where?: (offset: number) => string) => CheckResult;
