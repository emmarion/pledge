import { fileURLToPath } from "node:url";

const { check } = await import(fileURLToPath(new URL("../../src/check.ts", import.meta.url)));
const entryText = e =>
  `${e.names.join(",") || `?${e.origin.kind}`} : ${e.type.text}${e.rule ? ` is ${e.rule.text}` : ""}`;

export const verdict = (source, phase) => {
  const r = check(source, phase);
  return {
    error: r.error && { pos: r.error.span.start, message: r.error.message() },
    prints: r.prints.map(p => ({ pos: p.span.start, value: p.value })),
    qed: r.qed,
    goalProved: r.goalProved,
    containsSorry: r.containsSorry,
    inspects: r.inspects.map(i => ({ pos: i.span.start, text: i.info.scope.map(entryText).join("\n") })),
  };
};
