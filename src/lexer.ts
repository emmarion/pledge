import type { Phase, Span } from "./syntax.ts";
import type { Diagnostic } from "./api.ts";

export type Token =
  | { kind: "name"; text: string; span: Span }
  | { kind: "keyword"; text: string; span: Span }
  | { kind: "punct"; text: string; span: Span }
  | { kind: "underscore"; text: "_"; span: Span }
  | { kind: "eof"; text: ""; span: Span }
  | { kind: "error"; text: ""; span: Span; diag: Diagnostic };

const phase1Keywords = ["comptime", "data", "fn", "goal", "inspect", "is", "let", "match", "mutual", "print", "qed", "same", "sorry", "subterm"];
const phase2Keywords = ["erased", "many"];

const keywords = (phase: Phase): Set<string> =>
  new Set(phase >= 2 ? [...phase1Keywords, ...phase2Keywords] : phase1Keywords);

const puncts = ["=>", "->", "(", ")", "{", "}", ",", ";", ":", "="];
const isWordChar = (c: string): boolean => /[A-Za-z0-9_]/.test(c);

export function lex(source: string, phase: Phase): Token[] {
  const reserved = keywords(phase);
  const tokens: Token[] = [];
  const error = (start: number, end: number, message: () => string): Token[] => {
    tokens.push({ kind: "error", text: "", span: { start, end }, diag: { span: { start, end }, message } });
    return tokens;
  };
  let i = 0;
  while (i < source.length) {
    const c = source[i]!;
    const code = source.codePointAt(i)!;
    if (code > 0x7f) {
      const char = String.fromCodePoint(code);
      return error(i, i + new TextEncoder().encode(char).length, () => `non-ASCII character ${JSON.stringify(char)}; source text is ASCII`);
    }
    if (/\s/.test(c)) { i++; continue; }
    if (source.startsWith("--", i)) {
      while (i < source.length && source[i] !== "\n" && source.charCodeAt(i) <= 0x7f) i++;
      continue;
    }
    if (isWordChar(c)) {
      const start = i;
      while (i < source.length && isWordChar(source[i]!)) i++;
      const text = source.slice(start, i);
      const span = { start, end: i };
      if (text === "_") tokens.push({ kind: "underscore", text, span });
      else if (!/^[A-Za-z]/.test(text)) return error(start, i, () => `${JSON.stringify(text)} is not a name: a name starts with a letter`);
      else tokens.push({ kind: reserved.has(text) ? "keyword" : "name", text, span });
      continue;
    }
    const punct = puncts.find(p => source.startsWith(p, i));
    if (punct === undefined) return error(i, i + 1, () => `unexpected character ${JSON.stringify(c)}`);
    tokens.push({ kind: "punct", text: punct, span: { start: i, end: i + punct.length } });
    i += punct.length;
  }
  tokens.push({ kind: "eof", text: "", span: { start: source.length, end: source.length } });
  return tokens;
}
