export function lineCol(source: string, offset: number): { line: number; col: number } {
  const lines = source.slice(0, offset).split("\n");
  return { line: lines.length, col: (lines.at(-1) ?? "").length + 1 };
}

export const position = (source: string) => (offset: number): string => {
  const { line, col } = lineCol(source, offset);
  return `${line}:${col}`;
};

export const starts = (texts: readonly string[]): number[] => {
  let at = 0;
  return texts.map(t => { const start = at; at += t.length + 1; return start; });
};

export function locate(texts: readonly string[], offset: number): { index: number; local: number } {
  const from = starts(texts), index = from.reduce((found, s, i) => s <= offset ? i : found, 0);
  return { index, local: Math.min(offset - from[index]!, texts[index]!.length) };
}

export function place(texts: readonly string[], offset: number, box: (n: number) => string, line: string): string {
  const { index, local } = locate(texts, offset), at = lineCol(texts[index]!, local);
  return `${texts.length > 1 ? box(index + 1) : ""}${line}${at.line}:${at.col}`;
}

export const spot = (texts: readonly string[], offset: number): string => place(texts, offset, n => `box${n}:`, "");
