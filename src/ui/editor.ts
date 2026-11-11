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

const runs = (text: string, { start, end }: Span, cls: string): Decoration[] =>
  [...text.slice(start, end).matchAll(/\S(?:[^\n]*\S)?/g)]
    .map(m => ({ start: start + m.index, end: start + m.index + m[0].length, cls }));

const errorMarks = (text: string, span: Span): Decoration[] => {
  const { start } = span, marks = runs(text, span, "hl-error");
  const atBreak = start >= text.length || text[start] === "\n";
  return [...atBreak ? [{ start, end: start, cls: "hl-error" }] : marks.length ? []
    : [{ start, end: start + 1, cls: "hl-error" }], ...marks];
};

const edited = (spans: Span[], before: string, after: string): Span[] => {
  const shortest = Math.min(before.length, after.length), grown = after.length - before.length;
  let head = 0, tail = 0;
  while (head < shortest && before[head] === after[head]) head++;
  while (tail < shortest - head && before.at(-1 - tail) === after.at(-1 - tail)) tail++;
  const moved = (offset: number): number => offset <= head ? offset
    : Math.max(offset, before.length - tail) + grown;
  return spans.map(s => ({ start: moved(s.start), end: moved(s.end) })).filter(s => s.start < s.end);
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
  const queue = [...decorations].sort((a, b) => a.start - b.start);
  let open: Decoration[] = [], taken = 0;
  const span = (start: number, covering: Decoration[], content: string): HTMLElement | string => covering.length
    ? h("span", { class: covering.map(d => d.cls).join(" "), "data-at": `${start}` }, content) : content;
  return cuts.flatMap((start, i) => {
    while (taken < queue.length && queue[taken]!.start <= start) open.push(queue[taken++]!);
    open = open.filter(d => d.end > start || d.start === start);
    const empty = open.filter(d => d.end === start);
    return [...empty.length ? [span(start, empty, " ")] : [],
      ...i + 1 < cuts.length ? [span(start, open.filter(d => d.end > start), text.slice(start, cuts[i + 1]))] : []];
  });
};

const decorate = (text: string, tokens: Token[], kinds: Kinds, extra: Decoration[] = []): Decoration[] => [
  ...tokens.flatMap(t => {
    const cls = tokenClass(t, kinds);
    return cls ? [{ ...t.span, cls }] : [];
  }),
  ...comments(text, tokens),
  ...extra,
];

export const highlight = (text: string, tokens: Token[], kinds: Kinds): (HTMLElement | string)[] =>
  segments(text, decorate(text, tokens, kinds));

interface Line { key: string; row: HTMLElement }

function reuse(parent: HTMLElement, old: Line[], keys: string[], build: (i: number) => Child): Line[] {
  const spare = new Map<string, HTMLElement[]>();
  for (const { key, row } of old) spare.set(key, [...spare.get(key) ?? [], row]);
  const lines = keys.map((key, i) => ({ key, row: spare.get(key)?.shift() ?? h("div", {}, build(i)) }));
  lines.forEach(({ row }, i) => {
    if (parent.children[i] !== row) parent.insertBefore(row, parent.children[i] ?? null);
  });
  while (parent.children.length > lines.length) parent.lastChild!.remove();
  return lines;
}

const within = (r: DOMRect, x: number, y: number): boolean => x >= r.left && x < r.right && y >= r.top && y < r.bottom;

const following = (e: MouseEvent | KeyboardEvent): boolean =>
  /Mac|iPhone|iPad/.test(navigator.platform) ? e.metaKey : e.ctrlKey;

export class Editor {
  readonly area: HTMLTextAreaElement;
  readonly root: HTMLElement;
  private readonly gutter = h("div", { class: "gutter", "aria-hidden": "true" });
  private readonly layer = h("div", { class: "layer", "aria-hidden": "true" });
  private readonly caretLine = h("div", { class: "caret-line", "aria-hidden": "true" });
  private readonly code = h("div", { class: "code" }, this.caretLine, this.layer);
  private readonly outputs = h("div", { class: "outputs" });
  private lines: Line[] = [];
  private numbers: Line[] = [];
  private tokens: Token[] = [];
  private pairs = new Map<Token, Token>();
  private mark: Span | null = null;
  private erased: Span[] = [];
  private shown: string;
  private hovered: Token | null = null;
  private hoverTimer = 0;
  private link: Span | null = null;
  private linking: Token | null = null;
  private pointer: MouseEvent | null = null;

  constructor(text: string, editable: boolean, label: string | null, private readonly phase: () => Phase,
    private readonly firstLine: () => number,
    onEdit: () => void, onCaret: () => void, private readonly describe: (token: Token) => Promise<Child>,
    private readonly kinds: (offset: number, name: string) => NameKind | null | undefined,
    private readonly follow: (token: Token, go: boolean) => Promise<boolean>) {
    this.area = h("textarea", {
      class: "source", wrap: "off", spellcheck: "false", autocomplete: "off", autocapitalize: "off",
      readonly: !editable, "aria-label": editable ? "Your program" : "Read-only source",
    });
    this.area.value = this.shown = text;
    this.area.addEventListener("input", () => { onEdit(); this.show(null, null); });
    for (const event of ["keyup", "click", "focus", "select"]) this.area.addEventListener(event, onCaret);
    for (const event of ["focus", "blur"]) this.area.addEventListener(event, () => this.paint());
    document.addEventListener("selectionchange", () => { if (document.activeElement === this.area) this.paint(); });
    this.area.addEventListener("scroll", () => this.scrolled());
    addEventListener("scroll", () => this.hover(null), true);
    this.area.addEventListener("mousemove", e => {
      this.pointer = e;
      this.hover(e);
      this.linkAt(following(e));
    });
    for (const event of ["mouseleave", "keydown", "mousedown"]) this.area.addEventListener(event,
      () => this.hover(null));
    this.area.addEventListener("mouseleave", () => { this.pointer = null; this.linkAt(false); });
    this.area.addEventListener("mousedown", e => this.go(following(e) && this.at(e)?.token, e));
    this.area.addEventListener("keydown", e => e.key === "F12" && this.go(this.tokens.find(t => t.kind === "name"
      && t.span.start <= this.caret && this.caret <= t.span.end), e));
    for (const event of ["keydown", "keyup"] as const) addEventListener(event, e => this.linkAt(following(e)));
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

  show(mark: Span | null, outputs: Output[] | null, erased?: { spans: Span[]; keepFrom: number }): void {
    this.mark = mark;
    this.link = this.linking = null;
    const kept = edited(this.erased, this.shown, this.text);
    this.erased = erased ? [...erased.spans, ...kept.filter(s => s.start >= erased.keepFrom)] : kept;
    this.shown = this.text;
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
      class: "output", "data-line": `${this.firstLine() + line - 1}`,
      style: `top: ${padding + (line - 1) * lineHeight}px; --rows: ${(starts[i + 1] ?? lines.length + 1) - line}`,
    }, byLine.get(line)!)));
  }

  paint(): void {
    const text = this.text;
    const focused = document.activeElement === this.area;
    const caret = focused && this.area.selectionStart === this.area.selectionEnd ? this.caret : null;
    const paired = [...this.pairs.keys()];
    const bracket = caret === null ? undefined : paired.find(t => t.span.start === caret)
      ?? paired.find(t => t.span.end === caret);
    const decorations = decorate(text, this.tokens, t => this.kinds(t.span.start, t.text), [
      ...this.mark ? errorMarks(text, this.mark) : [],
      ...this.erased.flatMap(s => runs(text, s, "hl-erased")),
      ...bracket ? [bracket, this.pairs.get(bracket)!].map(t => ({ ...t.span, cls: "hl-bracket" })) : [],
      ...this.link ? [{ ...this.link, cls: "hl-link" }] : [],
    ]).sort((a, b) => a.start - b.start);
    let from = 0, taken = 0;
    const rows = text.split("\n").map(line => {
      const own: Decoration[] = [], end = from + line.length;
      for (; taken < decorations.length && decorations[taken]!.start <= end; taken++) {
        const d = decorations[taken]!;
        own.push({ start: d.start - from, end: d.end - from, cls: d.cls });
      }
      from = end + 1;
      return { line, own };
    });
    this.lines = reuse(this.layer, this.lines, rows.map(r => JSON.stringify(r)),
      i => segments(rows[i]!.line, rows[i]!.own));
    const line = (offset: number | null) => offset === null ? 0 : lineCol(text, offset).line;
    const errorLine = line(this.mark && this.mark.start);
    const caretLine = focused ? line(this.area.selectionStart) : 0;
    const first = this.firstLine(), numbers = rows.map((_, i) => ({ text: `${first + i}`,
      cls: [i + 1 === errorLine && "error-line", i + 1 === caretLine && "current"].filter(Boolean).join(" ") }));
    this.numbers = reuse(this.gutter, this.numbers, numbers.map(n => JSON.stringify(n)),
      i => h("span", { class: numbers[i]!.cls }, numbers[i]!.text));
    this.caretLine.hidden = !caretLine;
    this.caretLine.style.top = `${padding + (caretLine - 1) * lineHeight}px`;
    this.area.classList.toggle("following", this.link !== null);
    this.scrolled();
  }

  private scrolled(): void {
    this.code.style.setProperty("--scroll-x", `${-this.area.scrollLeft}px`);
    this.code.style.setProperty("--scroll-y", `${-this.area.scrollTop}px`);
  }

  private at(e: MouseEvent, holes = false): { token: Token; el: HTMLElement } | null {
    const el = [...this.layer.querySelectorAll<HTMLElement>(holes ? ".hl-name, .hl-hole" : ".hl-name")]
      .find(el => within(el.getBoundingClientRect(), e.clientX, e.clientY));
    if (!el) return null;
    const row = this.lines.findIndex(l => l.row === el.parentElement);
    const offset = this.text.split("\n").slice(0, row).reduce((sum, line) => sum + line.length + 1, 0)
      + Number(el.dataset.at);
    const token = this.tokens.find(t => (t.kind === "name" || holes && t.kind === "underscore")
      && t.span.start <= offset && offset < t.span.end);
    return token ? { token, el } : null;
  }

  private go(token: Token | false | undefined, e: Event): void {
    if (!token) return;
    e.preventDefault();
    void this.follow(token, true);
  }

  private linkAt(on: boolean): void {
    const token = on && this.pointer ? this.at(this.pointer)?.token ?? null : null;
    if (token === this.linking) return;
    this.linking = token;
    const show = (link: Span | null): void => {
      if (this.linking !== token || this.link === link) return;
      this.link = link;
      this.paint();
    };
    if (!token) return show(null);
    void this.follow(token, false).then(ok => show(ok ? token.span : null));
  }

  private hover(e: MouseEvent | null): void {
    const found = e && this.at(e, true), token = found?.token ?? null, at = found?.el;
    if (token === this.hovered) return;
    this.hovered = token;
    clearTimeout(this.hoverTimer);
    tip.hidden = true;
    if (!token || !at) return;
    this.hoverTimer = setTimeout(async () => {
      const content = await this.describe(token);
      if (!content || this.hovered !== token) return;
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
