import type { CheckResult, EntryId, EntryInfo, PositionInfo } from "../api.ts";
import { check } from "../check.ts";
import { lex } from "../lexer.ts";
import type { Phase, Span } from "../syntax.ts";
import { fill, h, lineCol, load, save, type Child } from "./dom.ts";
import { Editor } from "./editor.ts";
import { evalView, explainView, infoView, inspectView, statusView, type Ctx } from "./panels.ts";

export interface Box { text: string; key: string | null; holdsQed?: boolean }

const holdsQed = (text: string, phase: Phase): boolean =>
  lex(text, phase).some(t => t.kind === "keyword" && t.text === "qed");

export class Workspace implements Ctx {
  readonly editors: Editor[];
  readonly status = h("div", { class: "status", role: "status" });
  readonly panels = h("div", { class: "panels" });
  readonly tools: HTMLElement;
  private readonly explanation = h("div", { class: "explanation" });
  private readonly evaluation = h("div", { class: "evaluation" });
  private readonly query = h("input", { type: "text", class: "query", spellcheck: "false", placeholder: "a type or an expression", "aria-label": "Type or expression" });
  private result: CheckResult | null = null;
  private known = new Map<EntryId, EntryInfo>();
  private active = 0;
  private timer = 0;
  globalsOpen = false;

  constructor(private readonly boxes: Box[], private readonly phase: () => Phase) {
    this.editors = boxes.map((box, i) => new Editor(box.key === null ? box.text : load(box.key) ?? box.text, box.key !== null,
      () => {
        if (box.key !== null) save(box.key, this.editors[i]!.text);
        clearTimeout(this.timer);
        this.timer = setTimeout(() => this.run(), 200);
      },
      clicked => { this.active = i; this.refresh(); if (clicked) this.explain(this.caret(), true); }));
    this.active = boxes.length - 1;
    this.tools = h("div", { class: "tools" },
      h("div", { class: "row" }, h("button", { type: "button", onclick: () => this.explain(this.caret()) }, "Explain the term at the caret")),
      this.explanation,
      h("form", { class: "row", onsubmit: (e: Event) => { e.preventDefault(); this.evaluate(); } },
        h("label", {}, "At the caret: ", this.query), h("button", { type: "submit" }, "Check")),
      this.evaluation);
  }

  get showErased(): boolean { return this.phase() >= 2; }

  private starts(): number[] {
    let at = 0;
    return this.editors.map(e => { const start = at; at += e.text.length + 1; return start; });
  }

  private locate(offset: number): { index: number; local: number } {
    const starts = this.starts();
    const index = starts.reduce((found, s, i) => s <= offset ? i : found, 0);
    return { index, local: Math.min(offset - starts[index]!, this.editors[index]!.text.length) };
  }

  private within(index: number, span: Span): Span | null {
    const start = this.starts()[index]!;
    const length = this.editors[index]!.text.length;
    return this.locate(span.start).index === index ? { start: span.start - start, end: Math.min(span.end - start, length) } : null;
  }

  private caret(): number { return this.starts()[this.active]! + this.editors[this.active]!.caret; }

  where(offset: number): string {
    const { index, local } = this.locate(offset);
    const { line, col } = lineCol(this.editors[index]!.text, local);
    return `${this.editors.length > 1 ? `box ${index + 1}, ` : ""}line ${line}:${col}`;
  }

  entry(id: EntryId): EntryInfo | undefined { return this.known.get(id); }

  goto(offset: number): void {
    const { index, local } = this.locate(offset);
    this.active = index;
    this.editors[index]!.setCaret(local);
    this.refresh();
  }

  explain(offset: number, quiet = false): void {
    const result = this.result?.explainAt(offset);
    if (result !== undefined) fill(this.explanation, result === null && quiet ? null : explainView(result, this));
  }

  private evaluate(): void {
    if (this.result) fill(this.evaluation, evalView(this.result.evalAt(this.caret(), this.query.value), this));
  }

  private remember(infos: PositionInfo[]): void {
    for (const info of infos) for (const e of info.scope) this.known.set(e.id, e);
  }

  run(): void {
    fill(this.explanation);
    fill(this.evaluation);
    try {
      this.result = check(this.editors.map(e => e.text).join("\n"), this.phase());
    } catch (e) {
      this.result = null;
      fill(this.status, h("span", { class: "verdict bad" }, `Internal error in the checker: ${String(e)}`));
      fill(this.panels);
      return;
    }
    const r = this.result;
    const error = r.error && r.error.message();
    this.known = new Map();
    this.remember(r.inspects.map(i => i.info));
    const outputs = [
      ...r.error ? [{ span: r.error.span, node: h("span", { class: "error", title: error ?? "" }, error) }] : [],
      ...r.prints.map(p => ({ span: p.span, node: h("code", { class: "print", title: p.value }, p.value) })),
      ...r.inspects.map(i => ({ span: i.span, node: inspectView(i.info, this) })),
    ];
    this.editors.forEach((editor, index) => {
      const local = (span: Span) => this.within(index, span);
      editor.show(r.error && local(r.error.span), outputs.flatMap(({ span, node }) => {
        const at = local(span);
        return at ? [{ line: lineCol(editor.text, at.start).line, node }] : [];
      }));
    });
    fill(this.status, statusView(r, error, this.boxes.some((box, i) => box.holdsQed && !holdsQed(this.editors[i]!.text, this.phase())), this));
    this.refresh();
  }

  private refresh(): void {
    if (!this.result) return;
    const info = this.result.infoAt(this.caret());
    this.remember([info]);
    fill(this.panels, infoView(info, this));
  }

  reset(): void {
    this.boxes.forEach((box, i) => {
      if (box.key === null) return;
      this.editors[i]!.area.value = box.text;
      save(box.key, box.text);
    });
    this.run();
  }

  mount(header: Child, resetLabel: string, intro: Child = null, outro: Child = null, nav: Child = null): void {
    document.body.append(
      h("header", { class: "top" }, header),
      h("main", { class: nav ? "layout tutorial" : "layout" }, nav,
        h("div", { class: "work" }, intro, this.editors.map(e => e.root),
          h("div", { class: "row" }, h("button", { type: "button", onclick: () => this.reset() }, resetLabel)),
          this.status, this.tools, outro),
        h("aside", { class: "side" }, this.panels)));
    this.run();
  }
}
