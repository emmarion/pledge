import type { Span } from "../syntax.ts";
import { fill, h, lineCol } from "./dom.ts";

export interface Output { line: number; node: Node }

const lineHeight = 21;
const padding = 8;
const scrollbar = 16;

const marked = (text: string): string => text === "" || text.startsWith("\n") ? ` ${text}` : text;

export class Editor {
  readonly area: HTMLTextAreaElement;
  readonly root: HTMLElement;
  private readonly gutter = h("pre", { class: "gutter", "aria-hidden": "true" });
  private readonly backdrop = h("pre", { class: "backdrop", "aria-hidden": "true" });
  private readonly outputs = h("div", { class: "outputs" });

  constructor(text: string, editable: boolean, onEdit: () => void, onCaret: (clicked: boolean) => void) {
    this.area = h("textarea", {
      class: "source", wrap: "off", spellcheck: "false", autocomplete: "off", autocapitalize: "off",
      readonly: !editable, "aria-label": editable ? "Your program" : "Read-only source",
    });
    this.area.value = text;
    this.area.addEventListener("input", () => { this.show(null, null); onEdit(); });
    for (const event of ["keyup", "click", "focus", "select"]) this.area.addEventListener(event, () => onCaret(event === "click"));
    this.area.addEventListener("scroll", () => { this.backdrop.scrollLeft = this.area.scrollLeft; });
    this.root = h("div", { class: editable ? "editor" : "editor readonly" },
      this.gutter, h("div", { class: "code" }, this.backdrop, this.area), this.outputs);
    this.show(null, []);
  }

  get text(): string { return this.area.value; }

  get caret(): number { return this.area.selectionStart; }

  setCaret(offset: number): void {
    this.area.focus();
    this.area.setSelectionRange(offset, offset);
    const top = this.area.getBoundingClientRect().top + padding + (lineCol(this.text, offset).line - 1) * lineHeight;
    if (top < 0 || top > innerHeight - lineHeight) scrollBy({ top: top - innerHeight / 3 });
  }

  show(mark: Span | null, outputs: Output[] | null): void {
    const text = this.text;
    const lines = text.split("\n").length;
    this.area.style.height = `${lines * lineHeight + 2 * padding + scrollbar}px`;
    fill(this.gutter, Array.from({ length: lines }, (_, i) => `${i + 1}`).join("\n"));
    fill(this.backdrop, mark
      ? [text.slice(0, mark.start), h("mark", {}, marked(text.slice(mark.start, mark.end))), text.slice(mark.end)]
      : text, "\n");
    if (outputs === null) return;
    const byLine = new Map<number, Node[]>();
    for (const { line, node } of outputs) byLine.set(line, [...byLine.get(line) ?? [], node]);
    fill(this.outputs, [...byLine].map(([line, nodes]) =>
      h("div", { class: "output", style: `top: ${padding + (line - 1) * lineHeight}px` }, nodes)));
  }
}
