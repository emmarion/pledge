import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { check } from "../src/check.ts";
import type { CheckResult, Diagnostic, EntryInfo, PositionInfo } from "../src/api.ts";
import type { Phase } from "../src/syntax.ts";
import * as examples from "../src/examples.ts";

const at = (dir: string): URL => new URL(`../${dir}/`, import.meta.url);
export const file = (name: string, dir = "tests"): string => readFileSync(new URL(name, at(dir)), "utf8");
export const files = (prefix = "", dir = "tests"): string[] =>
  readdirSync(at(dir)).filter(f => f.startsWith(prefix) && f.endsWith(".pledge"));

export const nat = `${examples.nat}\n`;
export const vecBy = (mult: string): string => `${examples.vecBy(mult)}\n`;
export const vheadBy = (mult: string): string => `${examples.vheadBy(mult)}\n`;
export const isZero = "data IsZero(n : Nat()) : Type() {\n  IsZeroHere() : IsZero(Zero());\n}\n";

export const qedChecks = (r: CheckResult): boolean | null => r.qed === "none" ? null : r.qed === "checks";
export const verdicts = (r: CheckResult) => [r.containsSorry, qedChecks(r), r.goalProved];
const shown = (type: string | undefined, rule: string | undefined): string =>
  `${type}${rule === undefined ? "" : ` is ${rule}`}`;
const entryText = (e: EntryInfo): string =>
  `${e.names.join(",") || e.marker} : ${shown(e.canonical.type.term.text, e.canonical.rule?.term.text)}`;
export const listed = (info: PositionInfo): EntryInfo[] => [...info.globalEntries, ...info.scope];
export const scopeOf = (info: PositionInfo): string[] => info.scope.map(entryText);
export const globalEntriesOf = (info: PositionInfo): string[] => info.globalEntries.map(entryText);
export const entriesOf = (info: PositionInfo): string[] => [...globalEntriesOf(info), ...scopeOf(info)];
export const namedOf = (info: PositionInfo): string[] => listed(info).filter(e => e.names.length).map(entryText);
export const explainTerm = (r: CheckResult, at: number) => {
  const x = r.explainAt(at);
  return x && "canonical" in x ? x : null;
};
export const standsFor = (r: CheckResult, at: number): string[] | null => {
  const x = r.explainAt(at);
  return x && "stands" in x ? x.stands.map(e => `${e.erased ? "erased " : ""}${e.name ?? "_"} : ` +
    shown(e.canonical.type?.term.text, e.canonical.rule?.term.text)) : null;
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
