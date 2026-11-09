import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { check } from "../src/check.ts";
import type { CheckResult, Diagnostic, EntryInfo, PositionInfo } from "../src/api.ts";
import type { Phase } from "../src/syntax.ts";
import * as examples from "../src/examples.ts";

const dir = new URL("./", import.meta.url);
export const file = (name: string): string => readFileSync(new URL(name, dir), "utf8");
export const files = (prefix = ""): string[] =>
  readdirSync(dir).filter(f => f.startsWith(prefix) && f.endsWith(".pledge"));

export const nat = `${examples.nat}\n`;
export const vecBy = (mult: string): string => `${examples.vecBy(mult)}\n`;
export const vheadBy = (mult: string): string => `${examples.vheadBy(mult)}\n`;
export const isZero = "data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\n";

export const qedChecks = (r: CheckResult): boolean | null => r.qed === "none" ? null : r.qed === "checks";
export const verdicts = (r: CheckResult) => [r.containsSorry, qedChecks(r), r.goalProved];
const entryText = (e: EntryInfo): string =>
  `${e.names.join(",") || `?${e.origin.kind}`} : ${e.type.text}${e.rule ? ` is ${e.rule.text}` : ""}`;
export const scopeOf = (info: PositionInfo): string[] => info.scope.map(entryText);
export const explainTerm = (r: CheckResult, at: number) => {
  const x = r.explainAt(at);
  return x && "canonical" in x ? x : null;
};
export const standsFor = (r: CheckResult, at: number): string[] | null => {
  const x = r.explainAt(at);
  return x && "stands" in x ? x.stands.map(e => `${e.erased ? "erased " : ""}${e.name ?? "_"} : ${e.type?.text}${e.rule ? ` is ${e.rule.text}` : ""}`) : null;
};

export const harness = (phase: Phase) => ({
  ok(source: string, under: Phase = phase): CheckResult {
    const r = check(source, under);
    if (r.error) assert.fail(`unexpected error at ${r.error.span.start} ` +
      `(${JSON.stringify(source.slice(r.error.span.start, r.error.span.end))}): ${r.error.message()}`);
    return r;
  },
  err(source: string, at: string, pattern: RegExp, after = ""): Diagnostic {
    const r = check(source, phase);
    if (!r.error) return assert.fail("expected an error");
    const start = source.indexOf(at, after ? source.indexOf(after) : 0);
    assert.ok(start >= 0, `${at} is not in the source`);
    const message = r.error.message();
    assert.equal(source.slice(r.error.span.start, r.error.span.end), at, message);
    assert.equal(r.error.span.start, start, message);
    assert.match(message, pattern);
    assert.doesNotMatch(message, /internal|undefined|\[object/);
    return r.error;
  },
});
