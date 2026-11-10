import type { CheckResult } from "../api.ts";
import { check } from "../check.ts";
import { lex } from "../lexer.ts";
import { LAZY, type Checker, type Reply, type Request } from "./remote.ts";

let result: CheckResult;

const encode = (v: unknown): unknown => typeof v === "function" ? { [LAZY]: encode(v()) }
  : Array.isArray(v) ? v.map(encode)
    : v && typeof v === "object" ? Object.fromEntries(Object.entries(v).map(([key, x]) => [key, encode(x)])) : v;

const run: Checker["check"] = (texts, phase) => {
  const source = texts.join("\n");
  result = check(source, phase);
  const { infoAt, nameAt, explainAt, evalAt, ...summary } = result;
  return { ...summary, kinds: lex(source, phase).flatMap(t => {
    const n = t.kind === "name" && nameAt(t.span.start);
    return n ? [[t.span.start, n.kind === "entry" ? null : n.kind]] : [];
  }) };
};

addEventListener("message", ({ data: { id, method, args } }: MessageEvent<Request>) => {
  const reply = (r: Reply): void => postMessage(r);
  try {
    reply({ id, value: encode(method === "check" ? run(...args as Parameters<typeof run>)
      : (result[method] as (...args: unknown[]) => unknown)(...args)) });
  } catch (e) {
    reply({ id, error: String(e) });
  }
});
