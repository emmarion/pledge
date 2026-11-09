import type { Phase, Span } from "../syntax.ts";
import { lex, type Token } from "../lexer.ts";
import { lineCol } from "../position.ts";
import { fill, h, type Child } from "./dom.ts";

export type NameKind = "type" | "ctor" | "fn";

interface Output { line: number; node: Node }

interface Decoration { start: number; end: number; cls: string }

const lineHeight = 21;
const padding = 8;
const scrollbar = 16;
const hoverDelay = 400;

const brackets: Record<string, string> = { "(": ")", "{": "}" };

const tip = h("div", { class: "hover-tip", role: "tooltip", hidden: true });

type Kinds = (t: Token) => NameKind | null | undefined;

const tokenClass = (t: Token, kinds: Kinds): string | null =>
  t.kind === "name" ? `hl-name ${kinds(t) ? `hl-${kinds(t)}` : ""}`
    : t.kind === "keyword" ? "hl-keyword"
      : t.kind === "punct" ? "hl-punct"
        : t.kind === "underscore" ? "hl-hole"
          : t.kind === "error" ? "hl-lex-error"
            : null;

const comments = (text: string, tokens: Token[]): Decoration[] =>
  tokens.flatMap((t, i) => {
    const from = i ? tokens[i - 1]!.span.end : 0;
    return [...text.slice(from, t.span.start).matchAll(/--[^\n]*/g)]
      .map(m => ({ start: from + m.index, end: from + m.index + m[0].length, cls: "hl-comment" }));
  });

const errorMarks = (text: string, { start, end }: Span): Decoration[] => {
  const runs = [...text.slice(start, end).matchAll(/\S(?:[^\n]*\S)?/g)]
    .map(m => ({ start: start + m.index, end: start + m.index + m[0].length, cls: "hl-error" }));
  const atBreak = start >= text.length || text[start] === "\n";
  return [...atBreak ? [{ start, end: start, cls: "hl-error" }] : runs.length ? []
    : [{ start, end: start + 1, cls: "hl-error" }], ...runs];
};

const partners = (tokens: Token[]): Map<Token, Token> => {
  const pairs = new Map<Token, Token>();
  const open: Token[] = [];
  for (const t of tokens) {
    if (t.kind !== "punct") continue;
    if (t.text in brackets) open.push(t);
    else if (Object.values(brackets).includes(t.text)) {
      const opener = open.pop();
      if (opener && brackets[opener.text] === t.text) pairs.set(opener, t).set(t, opener);
    }
  }
  return pairs;
};

const columns = (line: string): number => [...line].reduce((col, c) => col + (c === "\t" ? 2 - col % 2 : 1), 0);

const segments = (text: string, decorations: Decoration[]): (HTMLElement | string)[] => {
  const cuts = [...new Set([0, text.length, ...decorations.flatMap(d => [d.start, d.end])])].sort((a, b) => a - b);
  const span = (start: number, covering: (d: Decoration) => boolean, content: string): HTMLElement | string => {
    const cls = decorations.filter(covering).map(d => d.cls).join(" ");
    return cls ? h("span", { class: cls, "data-at": `${start}` }, content) : content;
  };
  return cuts.flatMap((start, i) => [
    ...decorations.some(d => d.start === start && d.end === start)
      ? [span(start, d => d.start === start && d.end === start, " ")] : [],
    ...i + 1 < cuts.length ? [span(start, d => d.start <= start && cuts[i + 1]! <= d.end,
      text.slice(start, cuts[i + 1]))] : [],
  ]);
};

export const highlight = (text: string, tokens: Token[], kinds: Kinds,
  extra: Decoration[] = []): (HTMLElement | string)[] =>
  segments(text, [
    ...tokens.flatMap(t => {
      const cls = tokenClass(t, kinds);
      return cls ? [{ ...t.span, cls }] : [];
    }),
    ...comments(text, tokens),
    ...extra,
  ]);

const within = (r: DOMRect, x: number, y: number): boolean => x >= r.left && x < r.right && y >= r.top && y < r.bottom;

export class Editor {
  readonly area: HTMLTextAreaElement;
  readonly root: HTMLElement;
  private readonly gutter = h("div", { class: "gutter", "aria-hidden": "true" });
  private readonly layer = h("pre", { class: "layer", "aria-hidden": "true" });
  private readonly caretLine = h("div", { class: "caret-line", "aria-hidden": "true" });
  private readonly code = h("div", { class: "code" }, this.caretLine, this.layer);
  private readonly outputs = h("div", { class: "outputs" });
  private tokens: Token[] = [];
  private pairs = new Map<Token, Token>();
  private mark: Span | null = null;
  private hovered: Token | null = null;
  private hoverTimer = 0;

  constructor(text: string, editable: boolean, label: string | null, private readonly phase: () => Phase,
    onEdit: () => void, onCaret: () => void, private readonly describe: (offset: number) => Child,
    private readonly kinds: (offset: number, name: string) => NameKind | null | undefined) {
    this.area = h("textarea", {
      class: "source", wrap: "off", spellcheck: "false", autocomplete: "off", autocapitalize: "off",
      readonly: !editable, "aria-label": editable ? "Your program" : "Read-only source",
    });
    this.area.value = text;
    this.area.addEventListener("input", () => { onEdit(); this.show(null, null); });
    for (const event of ["keyup", "click", "focus", "select"]) this.area.addEventListener(event, onCaret);
    for (const event of ["focus", "blur"]) this.area.addEventListener(event, () => this.paint());
    document.addEventListener("selectionchange", () => { if (document.activeElement === this.area) this.paint(); });
    this.area.addEventListener("scroll", () => this.scrolled());
    addEventListener("scroll", () => this.hover(null), true);
    this.area.addEventListener("mousemove", e => this.hover(e));
    for (const event of ["mouseleave", "keydown", "mousedown"]) this.area.addEventListener(event,
      () => this.hover(null));
    this.code.append(this.area);
    this.root = h("div", { class: "box" }, label && h("div", { class: "box-label" }, label),
      h("div", { class: editable ? "editor" : "editor readonly" }, this.gutter, this.code, this.outputs));
    this.show(null, []);
  }

  get text(): string { return this.area.value; }

  get caret(): number { return this.area.selectionStart; }

  setCaret(offset: number): void {
    this.area.focus();
    this.area.setSelectionRange(offset, offset);
    const top = this.area.getBoundingClientRect().top + padding + (lineCol(this.text, offset).line - 1) * lineHeight;
    if (top < 0 || top > innerHeight - lineHeight) scrollBy({ top: top - innerHeight / 3 });
    this.paint();
  }

  show(mark: Span | null, outputs: Output[] | null): void {
    this.mark = mark;
    this.tokens = lex(this.text, this.phase());
    this.pairs = partners(this.tokens);
    const lines = this.text.split("\n");
    this.area.style.height = `${lines.length * lineHeight + 2 * padding + scrollbar}px`;
    this.code.style.setProperty("--cols", `${lines.reduce((widest, line) => Math.max(widest, columns(line)), 0)}`);
    this.paint();
    if (outputs === null) return;
    const byLine = new Map<number, Node[]>();
    for (const { line, node } of outputs) byLine.set(line, [...byLine.get(line) ?? [], node]);
    const starts = [...byLine.keys()].sort((a, b) => a - b);
    fill(this.outputs, starts.map((line, i) => h("div", {
      class: "output", "data-line": `${line}`,
      style: `top: ${padding + (line - 1) * lineHeight}px; --rows: ${(starts[i + 1] ?? lines.length + 1) - line}`,
    }, byLine.get(line)!)));
  }

  private paint(): void {
    const text = this.text;
    const focused = document.activeElement === this.area;
    const caret = focused && this.area.selectionStart === this.area.selectionEnd ? this.caret : null;
    const paired = [...this.pairs.keys()];
    const bracket = caret === null ? undefined : paired.find(t => t.span.start === caret)
      ?? paired.find(t => t.span.end === caret);
    fill(this.layer, highlight(text, this.tokens, t => this.kinds(t.span.start, t.text), [
      ...this.mark ? errorMarks(text, this.mark) : [],
      ...bracket ? [bracket, this.pairs.get(bracket)!].map(t => ({ ...t.span, cls: "hl-bracket" })) : [],
    ]), "\n");
    const line = (offset: number | null) => offset === null ? 0 : lineCol(text, offset).line;
    const errorLine = line(this.mark && this.mark.start);
    const caretLine = focused ? line(this.area.selectionStart) : 0;
    fill(this.gutter, Array.from({ length: text.split("\n").length }, (_, i) =>
      h("span", { class: [i + 1 === errorLine && "error-line", i + 1 === caretLine && "current"].filter(Boolean)
        .join(" ") }, `${i + 1}`)));
    this.caretLine.hidden = !caretLine;
    this.caretLine.style.top = `${padding + (caretLine - 1) * lineHeight}px`;
    this.scrolled();
  }

  private scrolled(): void {
    this.code.style.setProperty("--scroll-x", `${-this.area.scrollLeft}px`);
    this.code.style.setProperty("--scroll-y", `${-this.area.scrollTop}px`);
  }

  private hover(e: MouseEvent | null): void {
    const at = e && [...this.layer.querySelectorAll<HTMLElement>(".hl-name")]
      .find(el => within(el.getBoundingClientRect(), e.clientX, e.clientY));
    const offset = at ? Number(at.dataset.at) : -1;
    const token = this.tokens.find(t => t.kind === "name" && t.span.start <= offset && offset < t.span.end) ?? null;
    if (token === this.hovered) return;
    this.hovered = token;
    clearTimeout(this.hoverTimer);
    tip.hidden = true;
    if (!token || !at) return;
    this.hoverTimer = setTimeout(() => {
      const content = this.describe(token.span.start);
      if (!content) return;
      fill(tip, content);
      if (!tip.isConnected) document.body.append(tip);
      tip.hidden = false;
      const r = at.getBoundingClientRect();
      tip.style.left = `${Math.max(8, Math.min(r.left, innerWidth - tip.offsetWidth - 8))}px`;
      const below = r.bottom + tip.offsetHeight + 12 <= innerHeight;
      tip.style.top = `${below ? r.bottom + 6 : r.top - tip.offsetHeight - 6}px`;
    }, hoverDelay);
  }
}
