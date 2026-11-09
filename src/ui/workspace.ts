import type { CheckResult, EntryId, EntryInfo, NameInfo, PositionInfo } from "../api.ts";
import { check } from "../check.ts";
import { hasKeyword, lex, type Token } from "../lexer.ts";
import type { Phase, Span } from "../syntax.ts";
import { lineCol } from "../position.ts";
import { fill, h, load, save, type Child } from "./dom.ts";
import { Editor, highlight, type NameKind } from "./editor.ts";
import { marked } from "./links.ts";
import { entryTip, evalView, explainTip, explainView, globalsView, globalTip, infoView, inspectView, section,
  statusView, verdict, type Host } from "./panels.ts";

interface Box { text: string; key: string | null; holdsQed?: boolean }

interface ProgramSpec { label: string; boxes: number[] }

export interface Reset { label: string; question: string }

const kindOf = (n: NameInfo): NameKind | null => n.kind === "entry" ? null : n.kind;

const kindNames: Record<NameKind, string> = { fn: "fn", type: "type", ctor: "value constructor" };

class Program implements Host {
  result: CheckResult | null = null;
  status: Child = null;
  stale = false;
  private readonly kinds = new Map<string, NameKind | null>([["Type", "type"]]);
  private known = new Map<EntryId, EntryInfo>();

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

  spot(offset: number): string { return this.place(offset, n => `box${n}:`, ""); }

  entry(id: EntryId): EntryInfo | undefined { return this.known.get(id); }

  goto(offset: number): void {
    const { index, local } = this.locate(offset);
    this.ws.editors[this.members[index]!]!.setCaret(local);
    this.ws.select(this.members[index]!);
  }

  private named(box: number, local: number): NameInfo | null {
    return this.fresh()?.nameAt(this.offset(box, local)) ?? null;
  }

  private fresh(): CheckResult | null { return this.stale ? null : this.result; }

  describe(box: number, { kind, span }: Token): Child {
    if (kind === "underscore") {
      const x = this.fresh()?.explainAt(this.offset(box, span.start));
      return x && x.span.end === this.offset(box, span.end) ? explainTip(x, this.showErased) : null;
    }
    const n = this.named(box, span.start);
    return !n ? null : n.kind === "entry" ? entryTip(n.entry, this.showErased)
      : globalTip(kindNames[n.kind], n.name, n.signature);
  }

  kindAt(box: number, local: number, name: string): NameKind | null | undefined {
    const n = this.named(box, local);
    return n ? kindOf(n) : this.kinds.get(name);
  }

  info(offset: number): PositionInfo | null {
    const info = this.result?.infoAt(offset) ?? null;
    if (info) this.remember([info]);
    return info;
  }

  private remember(infos: PositionInfo[]): void {
    for (const info of infos) for (const e of info.scope) this.known.set(e.id, e);
  }

  run(): void {
    const phase = this.ws.phase();
    const source = this.editors.map(e => e.text).join("\n");
    this.stale = false;
    try {
      this.result = check(source, phase, offset => this.spot(offset));
    } catch (e) {
      this.result = null;
      this.status = verdict(false, `Internal error in the checker: ${String(e)}`);
      return;
    }
    const r = this.result;
    const error = r.error && r.error.message();
    for (const t of lex(source, phase)) {
      const n = t.kind === "name" && r.nameAt(t.span.start);
      if (n) this.kinds.set(t.text, kindOf(n));
    }
    this.known = new Map();
    this.remember(r.inspects.map(i => i.info));
    const outputs = [
      ...r.error ? [{ span: r.error.span,
        node: h("span", { class: "message bad", tabindex: "0" }, error && marked(error)) }] : [],
      ...r.prints.map(p => ({ span: p.span, node: h("code", { class: "message print", tabindex: "0" },
        highlight(p.value, lex(p.value, phase), t => this.kinds.get(t.text)).map(c => [c,
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
      }));
    });
    this.status = statusView(r, error, this.members.some(i => this.ws.boxes[i]!.holdsQed
      && !hasKeyword(this.ws.editors[i]!.text, phase, "qed")), this);
  }
}

export class Workspace {
  readonly editors: Editor[];
  readonly status = h("div", { class: "status", role: "status" });
  private readonly info = h("div", { class: "info" });
  private readonly term = h("div", {});
  private readonly answer = h("div", {});
  private readonly globals = h("div", {});
  private readonly query = h("input", { type: "text", class: "query", spellcheck: "false",
    placeholder: "a type or an expression", "aria-label": "Type or expression", oninput: () => this.refresh() });
  readonly panels = h("div", { class: "panels" }, this.info, section("Term", this.term),
    section("At the caret", h("form", { onsubmit: (e: Event) => { e.preventDefault(); this.refresh(); } },
      this.query), this.answer), this.globals);
  private readonly programs: Program[];
  private program: Program;
  private active: number;
  private timer = 0;
  globalsOpen = false;

  constructor(readonly boxes: Box[], readonly phase: () => Phase,
      programs: ProgramSpec[] = [{ label: "", boxes: boxes.map((_, i) => i) }]) {
    this.programs = programs.map(p => new Program(this, p.label, p.boxes));
    this.editors = boxes.map((box, i) => {
      const home = () => this.home(i);
      const members = home().members;
      return new Editor(box.key === null ? box.text : load(box.key) ?? box.text, box.key !== null,
        members.length > 1 ? `box ${members.indexOf(i) + 1}` : null, phase,
        () => {
          if (box.key !== null) save(box.key, this.editors[i]!.text);
          const affected = this.programs.filter(p => p.members.includes(i));
          for (const p of affected) p.stale = true;
          clearTimeout(this.timer);
          this.timer = setTimeout(() => this.run(affected), 200);
        },
        () => this.select(i), token => home().describe(i, token), (local, name) => home().kindAt(i, local, name));
    });
    this.program = this.programs[0]!;
    this.active = this.program.members.at(-1)!;
  }

  home(box: number): Program { return this.programs.find(p => p.members.includes(box))!; }

  private caret(): number { return this.program.offset(this.active, this.editors[this.active]!.caret); }

  select(box: number): void {
    this.program = this.home(box);
    this.active = box;
    this.refresh();
  }

  run(programs = this.programs): void {
    for (const p of programs) p.run();
    this.refresh();
  }

  private refresh(): void {
    const r = this.program.result, at = this.caret(), info = this.program.info(at);
    fill(this.status, this.programs.length > 1 && h("span", { class: "describing" },
      `Describing: ${this.program.label}`), this.program.status);
    fill(this.info, info && infoView(info, this.program));
    fill(this.term, r && explainView(r.explainAt(at), this.program));
    fill(this.answer, r && this.query.value.trim() && evalView(r.evalAt(at, this.query.value), this.program));
    fill(this.globals, info && globalsView(info, this.program));
  }

  private reset(question: string): void {
    const own = this.boxes.flatMap((box, i) => box.key === null ? [] : [{ ...box, key: box.key, i }]);
    if (own.some(b => this.editors[b.i]!.text !== b.text) && !confirm(question)) return;
    for (const b of own) {
      this.editors[b.i]!.area.value = b.text;
      save(b.key, b.text);
    }
    this.run();
  }

  mount(header: Child, reset: Reset, intro: Child = null, outro: Child = null, nav: Child = null): void {
    document.body.append(
      h("header", { class: "top" }, header),
      h("main", { class: nav ? "layout tutorial" : "layout" }, nav,
        h("div", { class: "work" }, intro, this.programs[0]!.members.map(i => this.editors[i]!.root),
          h("div", { class: "row" }, h("button", { type: "button", onclick: () => this.reset(reset.question) },
            reset.label)),
          this.status, outro),
        h("aside", { class: "side" }, this.panels)));
    this.run();
  }
}
