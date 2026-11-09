import type { Check, PositionInfo } from "./api.ts";

const nothing: PositionInfo = { expected: null, termination: null, scope: [], refutations: null, globals: [] };

export const check: Check = (_source, phase) => ({
  phase,
  error: null,
  containsSorry: false,
  qedChecks: null,
  goalProved: null,
  prints: [],
  inspects: [],
  infoAt: () => nothing,
  explainAt: () => null,
  evalAt: () => ({ error: { span: { start: 0, end: 0 }, message: () => "the checker is not written yet" } }),
});
