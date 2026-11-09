export function lineCol(source: string, offset: number): { line: number; col: number } {
  const lines = source.slice(0, offset).split("\n");
  return { line: lines.length, col: (lines.at(-1) ?? "").length + 1 };
}

export const position = (source: string) => (offset: number): string => {
  const { line, col } = lineCol(source, offset);
  return `${line}:${col}`;
};
