import type { CheckResult, EntryId, EntryInfo, Explained, PositionInfo } from "../api.ts";
import { hasKeyword, lex, type Token } from "../lexer.ts";
import type { Phase, Span } from "../syntax.ts";
import { lineCol, locate, position, starts } from "../position.ts";
import { fill, h, load, save, type Child } from "./dom.ts";
import { Editor, highlight, type NameKind } from "./editor.ts";
import { marked } from "./links.ts";
import { entryTip, evalView, explainTip, explainView, globalsView, globalTip, infoView, inspectView, section,
  statusView, verdict, type Host } from "./panels.ts";
import { remote, type Remote, type Summary } from "./remote.ts";

interface Box { text: string; key: string | null; holdsQed?: boolean }

interface ProgramSpec { label: string; boxes: number[] }

interface Look { info: PositionInfo; explained: Explained | null; answer: ReturnType<CheckResult["evalAt"]> | null }

const checkingAfter = 300;

const sideWidth = (px: number): void => document.documentElement.style.setProperty("--side", `${px}px`);

function resizer(): HTMLElement {
  const saved = Number(load("sideWidth"));
  if (saved) sideWidth(saved);
  const drag = (e: PointerEvent): void => {
    const px = Math.round(Math.min(Math.max(innerWidth - e.clientX - 24, 220), innerWidth * 0.7));
    sideWidth(px);
    save("sideWidth", String(px));
  };
  const bar: HTMLElement = h("div", { class: "resizer", title: "Drag to resize the panels", role: "separator",
    onpointerdown: (e: Event) => { bar.setPointerCapture((e as PointerEvent).pointerId); bar.onpointermove = drag; },
    onpointerup: () => { bar.onpointermove = null; } });
  return bar;
}

const kindNames: Record<NameKind, string> = { fn: "fn", type: "type", ctor: "value constructor" };

class Program implements Host {
  status: Child = null;
  checking = false;
  private stale = true;
  private holder: Remote | null = null;
  private pending: Remote | null = null;
  private busy = 0;
  private kindsAt: Map<number, NameKind | null>[] = [];
  private readonly kinds = new Map<string, NameKind | null>([["Type", "type"]]);
  private known = new Map<EntryId, EntryInfo>();

  constructor(private readonly ws: Workspace, readonly label: string, readonly members: number[]) {}

  get showErased(): boolean { return this.ws.phase() >= 2; }
  get opened(): Set<string> { return this.ws.opened; }

  private get editors(): Editor[] { return this.members.map(i => this.ws.editors[i]!); }

  private get texts(): string[] { return this.editors.map(e => e.text); }

  offset(box: number, local: number): number { return starts(this.texts)[this.members.indexOf(box)]! + local; }

  private within(index: number, span: Span): Span | null {
    const texts = this.texts, start = starts(texts)[index]!;
    return locate(texts, span.start).index === index ? { start: span.start - start,
      end: Math.min(span.end - start, texts[index]!.length) } : null;
  }

  at(offset: number): string { return position(this.texts.join("\n"))(offset); }

  where(offset: number): string { return `line ${this.at(offset)}`; }

  firstLine(box: number): number { return lineCol(this.texts.join("\n"), this.offset(box, 0)).line; }

  entry(id: EntryId): EntryInfo | undefined { return this.known.get(id); }

  goto(offset: number): void {
    const { index, local } = locate(this.texts, offset);
    this.ws.editors[this.members[index]!]!.setCaret(local);
    this.ws.select(this.members[index]!);
  }

  async describe(box: number, { kind, span }: Token): Promise<Child> {
    const r = this.stale ? null : this.holder, at = this.offset(box, span.start), end = this.offset(box, span.end);
    if (!r) return null;
    if (kind === "underscore") {
      const x = await r.call("explainAt", at);
      return x && x.span.end === end ? explainTip(x, this.showErased) : null;
    }
    const n = await r.call("nameAt", at);
    return !n ? null : n.kind === "entry" ? entryTip(n.entry, this.showErased)
      : globalTip(kindNames[n.kind], n.name, n.signature);
  }

  kindAt(box: number, local: number, name: string): NameKind | null | undefined {
    const kind = this.stale ? undefined : this.kindsAt[this.members.indexOf(box)]!.get(local);
    return kind === undefined ? this.kinds.get(name) : kind;
  }

  async look(offset: number, query: string): Promise<Look | null> {
    const r = this.holder;
    if (!r) return null;
    const [info, explained, answer] = await Promise.all([r.call("infoAt", offset), r.call("explainAt", offset),
      query.trim() ? r.call("evalAt", offset, query) : null]);
    if (r !== this.holder) return null;
    this.remember([info]);
    return { info, explained, answer };
  }

  private remember(infos: PositionInfo[]): void {
    for (const info of infos) for (const e of [...info.scope, ...info.globalEntries]) this.known.set(e.id, e);
  }

  outdate(): void {
    this.stale = true;
    this.pending?.close();
    this.pending = null;
    clearTimeout(this.busy);
  }

  run(): void {
    this.outdate();
    const phase = this.ws.phase(), texts = this.texts, next = this.pending = remote();
    this.busy = setTimeout(() => { this.checking = true; this.ws.showStatus(); }, checkingAfter);
    const settle = (holder: Remote | null, show: () => void) => {
      if (this.pending !== next) return;
      this.pending = null;
      clearTimeout(this.busy);
      this.holder?.close();
      this.holder = holder;
      this.stale = this.checking = false;
      show();
      this.ws.refresh();
    };
    next.call("check", texts, phase).then(r => settle(next, () => this.show(r, texts, phase)), e => {
      next.close();
      settle(null, () => { this.status = verdict(false, `Internal error in the checker: ${String(e)}`); });
    });
  }

  private show(r: Summary, texts: string[], phase: Phase): void {
    const error = r.error && r.error.message(), kinds = new Map(r.kinds);
    this.kindsAt = texts.map(() => new Map());
    for (const t of lex(texts.join("\n"), phase)) {
      const kind = kinds.get(t.span.start), { index, local } = locate(texts, t.span.start);
      if (kind === undefined) continue;
      this.kinds.set(t.text, kind);
      this.kindsAt[index]!.set(local, kind);
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
      }), { spans: r.erased.flatMap(span => local(span) ?? []),
        keepFrom: r.error ? r.error.span.start - starts(texts)[index]! : Infinity });
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
  private ticket = 0;
  readonly opened = new Set<string>(["Local entries"]);

  constructor(readonly boxes: Box[], readonly phase: () => Phase,
      programs: ProgramSpec[] = [{ label: "", boxes: boxes.map((_, i) => i) }]) {
    this.programs = programs.map(p => new Program(this, p.label, p.boxes));
    this.editors = boxes.map((box, i) => {
      const home = () => this.home(i);
      const members = home().members;
      return new Editor(box.key === null ? box.text : load(box.key) ?? box.text, box.key !== null,
        members.length > 1 ? `box ${members.indexOf(i) + 1}` : null, phase,
        () => this.editors ? home().firstLine(i) : 1,
        () => {
          for (const e of this.editors) e.paint();
          if (box.key !== null) save(box.key, this.editors[i]!.text);
          const affected = this.programs.filter(p => p.members.includes(i));
          for (const p of affected) p.outdate();
          clearTimeout(this.timer);
          this.timer = setTimeout(() => affected.forEach(p => p.run()), 200);
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

  run(): void {
    for (const e of this.editors) e.show(null, []);
    for (const p of this.programs) p.run();
  }

  showStatus(): void {
    const { label, status, checking } = this.program;
    fill(this.status, this.programs.length > 1 && h("span", { class: "describing" }, `Describing: ${label}`),
      checking && h("span", { class: "verdict checking" }, "Checking…"), status);
    this.status.classList.toggle("outdated", checking);
  }

  refresh(): void {
    const p = this.program, ticket = ++this.ticket;
    this.showStatus();
    void p.look(this.caret(), this.query.value).then(found => {
      if (ticket !== this.ticket) return;
      fill(this.info, found && infoView(found.info, p));
      fill(this.term, found && explainView(found.explained, p));
      fill(this.answer, found?.answer && evalView(found.answer, p));
      fill(this.globals, found && globalsView(found.info, p));
    });
  }

  replace(question: string, text = (box: Box): string => box.text, kept = (box: Box): string[] => [box.text]): boolean {
    const own = this.boxes.flatMap((box, i) => box.key === null ? [] : [{ box, key: box.key, i }]);
    if (own.some(b => !kept(b.box).includes(this.editors[b.i]!.text)) && !confirm(question)) return false;
    for (const b of own) {
      this.editors[b.i]!.area.value = text(b.box);
      save(b.key, text(b.box));
    }
    return true;
  }

  mount(header: Child, controls: Child, intro: Child = null, outro: Child = null, nav: Child = null): void {
    document.body.append(
      h("header", { class: "top" }, header),
      h("main", { class: nav ? "layout tutorial" : "layout" }, nav,
        h("div", { class: "work" }, intro, this.programs[0]!.members.map(i => this.editors[i]!.root),
          h("div", { class: "row" }, controls),
          this.status, outro),
        h("aside", { class: "side" }, resizer(), h("div", { class: "side-scroll" }, this.panels))));
    this.run();
  }
}
