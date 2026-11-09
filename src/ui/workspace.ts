import type { CheckResult, EntryId, EntryInfo, GlobalInfo, PositionInfo } from "../api.ts";
import { check } from "../check.ts";
import { hasKeyword, lex } from "../lexer.ts";
import type { Phase, Span } from "../syntax.ts";
import { lineCol } from "../position.ts";
import { fill, h, load, save, type Child } from "./dom.ts";
import { Editor, highlight, type NameKind } from "./editor.ts";
import { marked } from "./links.ts";
import { entryTip, evalView, explainView, globalTip, infoView, inspectView, statusView, verdict,
  type Host } from "./panels.ts";

interface Box { text: string; key: string | null; holdsQed?: boolean }

interface ProgramSpec { label: string; boxes: number[] }

const nameKinds = (globals: GlobalInfo[]): Map<string, NameKind> => new Map<string, NameKind>([["Type", "type"],
  ...globals.flatMap(g => g.kind === "binding" ? [] : [[g.name, g.kind] as const,
    ...(g.ctors ?? []).map(c => [c.name, "ctor"] as const)])]);

class Program implements Host {
  result: CheckResult | null = null;
  status: Child = null;
  stale = false;
  kinds = new Map<string, NameKind>();
  private known = new Map<EntryId, EntryInfo>();
  private globals: GlobalInfo[] = [];

  constructor(private readonly ws: Workspace, readonly label: string, readonly members: number[]) {}

  get showErased(): boolean { return this.ws.phase() >= 2; }
  get globalsOpen(): boolean { return this.ws.globalsOpen; }
  set globalsOpen(open: boolean) { this.ws.globalsOpen = open; }

  private get editors(): Editor[] { return this.members.map(i => this.ws.editors[i]!); }

  private starts(): number[] {
    let at = 0;
    return this.editors.map(e => { const start = at; at += e.text.length + 1; return start; });
  }

  offset(box: number, local: number): number { return this.starts()[this.members.indexOf(box)]! + local; }

  private locate(offset: number): { index: number; local: number } {
    const starts = this.starts();
    const index = starts.reduce((found, s, i) => s <= offset ? i : found, 0);
    return { index, local: Math.min(offset - starts[index]!, this.editors[index]!.text.length) };
  }

  private within(index: number, span: Span): Span | null {
    const start = this.starts()[index]!;
    const length = this.editors[index]!.text.length;
    return this.locate(span.start).index === index ? { start: span.start - start,
      end: Math.min(span.end - start, length) } : null;
  }

  private place(offset: number, box: (n: number) => string, line: string): string {
    const { index, local } = this.locate(offset);
    const at = lineCol(this.editors[index]!.text, local);
    return `${this.members.length > 1 ? box(index + 1) : ""}${line}${at.line}:${at.col}`;
  }

  where(offset: number): string { return this.place(offset, n => `box ${n}, `, "line "); }

  entry(id: EntryId): EntryInfo | undefined { return this.known.get(id); }

  goto(offset: number): void {
    const { index, local } = this.locate(offset);
    this.ws.editors[this.members[index]!]!.setCaret(local);
    this.ws.select(this.members[index]!);
  }

  explain(offset: number, quiet = false): void {
    const result = this.result?.explainAt(offset);
    if (result !== undefined) fill(this.ws.explanation, result === null && quiet ? null : explainView(result, this));
  }

  evaluate(offset: number, text: string): void {
    if (this.result) fill(this.ws.evaluation, evalView(this.result.evalAt(offset, text), this));
  }

  describe(offset: number, name: string): Child {
    if (!this.result || this.stale) return null;
    const entry = this.result.infoAt(offset).scope.find(e => e.names.includes(name));
    if (entry) return entryTip(entry, this.showErased);
    const global = this.globals.flatMap(g => [g, ...(g.ctors ?? []).map(c =>
      ({ ...c, kind: "value constructor" }))]).find(g => g.name === name);
    return global ? globalTip(global.kind, global.name, global.signature) : null;
  }

  panels(offset: number): Child {
    if (!this.result) return null;
    const info = this.result.infoAt(offset);
    this.remember([info]);
    return infoView(info, this);
  }

  private remember(infos: PositionInfo[]): void {
    for (const info of infos) for (const e of info.scope) this.known.set(e.id, e);
  }

  run(): void {
    const phase = this.ws.phase();
    const source = this.editors.map(e => e.text).join("\n");
    this.stale = false;
    try {
      this.result = check(source, phase, offset => this.place(offset, n => `box${n}:`, ""));
    } catch (e) {
      this.result = null;
      this.status = verdict(false, `Internal error in the checker: ${String(e)}`);
      return;
    }
    const r = this.result;
    const error = r.error && r.error.message();
    this.known = new Map();
    this.globals = r.infoAt(source.length).globals;
    if (this.globals.length) this.kinds = nameKinds(this.globals);
    this.remember(r.inspects.map(i => i.info));
    const outputs = [
      ...r.error ? [{ span: r.error.span,
        node: h("span", { class: "message bad", tabindex: "0" }, error && marked(error)) }] : [],
      ...r.prints.map(p => ({ span: p.span, node: h("code", { class: "message print", tabindex: "0" },
        highlight(p.value, lex(p.value, phase), this.kinds).map(c => [c,
          /[(,]$/.test(typeof c === "string" ? c : c.textContent!) && h("wbr")])) })),
      ...r.inspects.map(i => ({ span: i.span, node: inspectView(i.info, this) })),
    ];
    this.members.forEach((box, index) => {
      if (this.ws.home(box) !== this) return;
      const editor = this.ws.editors[box]!;
      const local = (span: Span) => this.within(index, span);
      editor.show(r.error && local(r.error.span), outputs.flatMap(({ span, node }) => {
        const at = local(span);
        return at ? [{ line: lineCol(editor.text, at.start).line, node }] : [];
      }), this.kinds);
    });
    this.status = statusView(r, error, this.members.some(i => this.ws.boxes[i]!.holdsQed
      && !hasKeyword(this.ws.editors[i]!.text, phase, "qed")), this);
  }
}

export class Workspace {
  readonly editors: Editor[];
  readonly status = h("div", { class: "status", role: "status" });
  readonly panels = h("div", { class: "panels" });
  readonly explanation = h("div", { class: "explanation" });
  readonly evaluation = h("div", { class: "evaluation" });
  readonly tools: HTMLElement;
  private readonly query = h("input", { type: "text", class: "query", spellcheck: "false",
    placeholder: "a type or an expression", "aria-label": "Type or expression" });
  private readonly programs: Program[];
  private program: Program;
  private active: number;
  private timer = 0;
  globalsOpen = false;

  constructor(readonly boxes: Box[], readonly phase: () => Phase,
      programs: ProgramSpec[] = [{ label: "", boxes: boxes.map((_, i) => i) }]) {
    this.programs = programs.map(p => new Program(this, p.label, p.boxes));
    this.editors = boxes.map((box, i) => new Editor(box.key === null ? box.text : load(box.key) ?? box.text,
      box.key !== null, phase,
      () => {
        if (box.key !== null) save(box.key, this.editors[i]!.text);
        const affected = this.programs.filter(p => p.members.includes(i));
        for (const p of affected) p.stale = true;
        clearTimeout(this.timer);
        this.timer = setTimeout(() => this.run(affected), 200);
      },
      clicked => { this.select(i); if (clicked) this.program.explain(this.caret(), true); },
      (offset, name) => this.home(i).describe(this.home(i).offset(i, offset), name)));
    this.program = this.programs[0]!;
    this.active = this.program.members.at(-1)!;
    this.tools = h("div", { class: "tools" },
      h("div", { class: "row" }, h("button", { type: "button", onclick: () => this.program.explain(this.caret()) },
        "Explain the term at the caret")),
      this.explanation,
      h("form", { class: "row",
        onsubmit: (e: Event) => { e.preventDefault(); this.program.evaluate(this.caret(), this.query.value); } },
        h("label", {}, "At the caret: ", this.query), h("button", { type: "submit" }, "Check")),
      this.evaluation);
  }

  home(box: number): Program { return this.programs.find(p => p.members.includes(box))!; }

  private caret(): number { return this.program.offset(this.active, this.editors[this.active]!.caret); }

  select(box: number): void {
    if (this.home(box) !== this.program) {
      this.program = this.home(box);
      fill(this.explanation);
      fill(this.evaluation);
    }
    this.active = box;
    this.refresh();
  }

  run(programs = this.programs): void {
    fill(this.explanation);
    fill(this.evaluation);
    for (const p of programs) p.run();
    this.refresh();
  }

  private refresh(): void {
    fill(this.status, this.programs.length > 1 && h("span", { class: "describing" },
      `Describing: ${this.program.label}`), this.program.status);
    fill(this.panels, this.program.panels(this.caret()));
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
        h("div", { class: "work" }, intro, this.programs[0]!.members.map(i => this.editors[i]!.root),
          h("div", { class: "row" }, h("button", { type: "button", onclick: () => this.reset() }, resetLabel)),
          this.status, this.tools, outro),
        h("aside", { class: "side" }, this.panels)));
    this.run();
  }
}
