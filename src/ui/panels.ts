import type { Canonical, CheckResult, EntryId, EntryInfo, ExpectedEntry, Explained, GlobalInfo, PositionInfo, Rendered,
  Rewrite } from "../api.ts";
import type { Span } from "../syntax.ts";
import { fill, h, type Child } from "./dom.ts";
import { linked, marked, unbroken } from "./links.ts";

export interface Host {
  goto(offset: number): void;
  entry(id: EntryId): EntryInfo | undefined;
  where(offset: number): string;
  at(offset: number): string;
  showErased: boolean;
  readonly opened: Set<string>;
}

const muted = (text: string): HTMLElement => h("span", { class: "muted" }, text);

const link = (text: Child, title: string, onclick: () => void): HTMLElement =>
  h("button", { class: "link", type: "button", title, onclick }, text);

const goto = (ctx: Host, offset: number, text: Child = ctx.where(offset)): HTMLElement =>
  link(text, `Go to ${ctx.where(offset)}`, () => ctx.goto(offset));

const declaredAt = (ctx: Host, at: Span, name: Child): HTMLElement =>
  link(name, `Declared at ${ctx.where(at.start)}`, () => ctx.goto(at.start));

const rendered = (r: Rendered, ctx: Host): HTMLElement => h("code", { class: "term" }, pieces(r, ctx));

function pieces(r: Rendered, ctx: Host): Child[] {
  const out: Child[] = [];
  let at = 0;
  for (const ref of [...r.refs].sort((a, b) => a.span.start - b.span.start || b.span.end - a.span.end)) {
    const { span } = ref;
    if (span.start < at) continue;
    const text = unbroken(r.text.slice(span.start, span.end));
    const info = "entry" in ref ? ctx.entry(ref.entry) : null, paren = "declared" in ref && r.text[span.end] === "(";
    const inner = (): Rendered => ({ text: r.text.slice(span.start, span.end), refs: r.refs.flatMap(q => q !== ref
      && q.span.start >= span.start && q.span.end <= span.end ? [{ ...q, span: { start: q.span.start - span.start,
        end: q.span.end - span.start } }] : []) });
    out.push(unbroken(r.text.slice(at, span.start)),
      "erased" in ref ? h("span", { class: "hl-erased" }, pieces(inner(), ctx))
      : "declared" in ref ? h("span", { class: "head" }, declaredAt(ctx, ref.declared, text), paren && "(")
      : info ? link(text, `${info.origin.kind} at ${ctx.where(info.origin.span.start)}`,
        () => ctx.goto(info.origin.span.start)) : text);
    at = span.end + (paren ? 1 : 0);
  }
  out.push(unbroken(r.text.slice(at)));
  return out;
}

const row = (term: string, value: Child): Child => [h("dt", {}, term), h("dd", {}, value)];

const tag = (text: string, show: boolean): Child => show && h("span", { class: "tag" }, text);

const typed = (name: Child, type: Child, rule: Child, erased: boolean): Child =>
  [h("span", { class: erased ? "name hl-erased" : "name" }, name), type && [" : ", type], rule && [" is ", rule],
    tag("erased", erased)];

const signed = (name: string, signature: Child): HTMLElement =>
  h("code", {}, h("span", { class: "name" }, name), signature);

const globalLine = (kind: string, name: string, signature: Child): Child =>
  [h("span", { class: "kind" }, kind), " ", signed(name, signature)];

export const section = (title: string, ...body: Child[]): HTMLElement =>
  h("section", { class: "panel" }, h("h3", {}, title), body);

const list = (items: Child[], empty: string): Child =>
  items.length ? h("ul", { class: "entries" }, items) : muted(empty);

const names = (e: EntryInfo): Child =>
  e.names.map((name, i) => [i > 0 && ", ", name, tag("tainted", e.tainted.includes(name))]);

const entryName = (e: EntryInfo, ctx: Host): Child =>
  goto(ctx, e.origin.span.start, e.names.length ? names(e) : h("span", { class: "marker" }, e.marker));

const expectedList = (entries: readonly ExpectedEntry[], ctx: Host): Child =>
  entries.length ? h("div", { class: "scope" }, entries.map(e => card([h("span", { class: "name" }, e.name ?? "_"),
    tag("erased", ctx.showErased && e.erased), tag("not determined", e.undetermined)], e, e.name ?? "_", ctx)))
    : muted("none");

const derivation = (lines: () => Rendered[], ctx: Host): HTMLElement =>
  h("ol", { class: "derivation" }, lines().map(step => h("li", {}, rendered(step, ctx))));

const expandable = (summary: Child, body: () => Child): HTMLElement => {
  const inside = h("div", {});
  return h("details", { ontoggle: () => { if (!inside.hasChildNodes()) fill(inside, body()); } },
    h("summary", {}, summary), inside);
};

const canonicalView = (title: Child, raw: Rendered, from: Child, c: Canonical, ctx: Host): Child[] => {
  const steps = c.rewrites(), number = (i: number): string => `(${i + 1})`;
  return [h("h4", {}, title),
    h("h5", {}, "Raw"), h("p", {}, rendered(raw, ctx), from),
    h("h5", {}, "Rules applied"), steps.length
      ? h("ol", { class: "rules" }, steps.map(s => h("li", {}, expandable(h("span", {}, rendered(s.rule, ctx), " ",
        muted("from "), goto(ctx, s.at.start, ctx.at(s.at.start))), () => derivation(s.how, ctx)))))
      : muted("None: the raw form is already canonical."),
    steps.length > 0 && [h("h5", {}, "Rewriting"), h("table", { class: "rewriting" },
      h("tr", {}, h("td", {}), h("td", {}, rendered(raw, ctx)), h("td", {})),
      steps.map((s, i) => h("tr", {}, h("td", {}, "="), h("td", {}, rendered(s.to, ctx)),
        h("td", {}, h("span", { class: "muted", title: s.rule.text }, `by ${number(i)}`)))))]];
};

const popover = (body: () => Child, closed = (): void => {}): HTMLElement => {
  const close = h("button", { class: "close", type: "button", title: "Close", "aria-label": "Close",
    onclick: () => pop.hidePopover() }, "\u00d7");
  const pop = h("div", { class: "canonical-pop", popover: "auto",
    ontoggle: (e: Event) => {
      if ((e as ToggleEvent).newState === "closed") closed();
      else if (!pop.hasChildNodes()) fill(pop, close, body());
    },
  });
  return pop;
};

const dialog = (text: Child, title: string, body: () => Child): Child[] => {
  const pop = popover(body);
  return [link(text, title, () => pop.togglePopover()), pop];
};

export function showDialog(body: () => Child): void {
  const pop = popover(body, () => pop.remove());
  document.body.append(pop);
  pop.showPopover();
}

export const usesView = (ctx: Host, name: string, introduced: string, def: Span, uses: readonly Span[],
  line: (offset: number) => Child): Child[] => [
  h("h4", {}, "Uses of ", h("code", {}, name)),
  h("p", {}, `${introduced} at `, goto(ctx, def.start), ": ", line(def.start)),
  uses.length ? h("ul", { class: "uses" }, uses.map(u => h("li", {}, goto(ctx, u.start), ": ", line(u.start))))
    : muted("No uses."),
];

const scopeRow = (label: string, title: Child, raw: Rendered, c: Canonical, ctx: Host, from: Child = null):
    HTMLElement =>
  h("tr", {}, h("th", {}, label), h("td", {}, rendered(c.term, ctx), (from || raw.text !== c.term.text) && [" ",
    dialog("steps", "Show the raw form and the rewrites that reach this canonical form",
      () => canonicalView(title, raw, from, c, ctx))]));

interface Shown {
  type: Rendered | null; rule: Rendered | null; ruleAt?: Span | null; typeAt?: Span; origin?: { span: Span };
  canonical: { type: Canonical | null; rule: Canonical | null };
}

const elsewhere = (at: Span | null | undefined, e: Shown, ctx: Host): Child =>
  at && e.origin && at.start !== e.origin.span.start && [" ", muted("from "), goto(ctx, at.start, ctx.at(at.start))];

const card = (head: Child, e: Shown, who: string, ctx: Host): HTMLElement => {
  const name = h("code", {}, who);
  return h("div", { class: "scope-entry" }, h("div", { class: "head" }, head), h("table", {},
    e.type && e.canonical.type && scopeRow("type", ["The type of ", name], e.type, e.canonical.type, ctx,
      elsewhere(e.typeAt, e, ctx)),
    e.rule && e.canonical.rule && scopeRow("is", ["The is rule of ", name], e.rule, e.canonical.rule, ctx,
      elsewhere(e.ruleAt, e, ctx))));
};

const scopeEntry = (e: EntryInfo, ctx: Host): HTMLElement => card([h("span", { class: "name" }, entryName(e, ctx)),
  tag("erased", ctx.showErased && e.erased)], e, e.names.join(", ") || e.marker, ctx);

export function infoView(info: PositionInfo, ctx: Host): HTMLElement[] {
  const { expected, termination, refutations } = info;
  return [
    section("Expected", expected.entries === null
      ? muted("Nothing is given here.")
      : expected.params
        ? [h("p", {}, "A function with parameters"), expectedList(expected.params, ctx), h("p", {}, "and returns"),
          expectedList(expected.entries, ctx)]
        : expectedList(expected.entries, ctx)),
    section("Termination", termination === null
      ? muted("Not inside a function.")
      : h("dl", {},
        row("Function", h("code", {}, termination.fn)),
        row("subterm parameters", termination.subtermParams.length
          ? h("code", {}, termination.subtermParams.join(", ")) : muted("none")),
        row("Group", h("code", {}, termination.group.join(", "))))),
    hidden(ctx, "Local entries", info.scope.length,
      info.taintedBy && h("p", { class: "muted" }, "This scope is tainted, so every result here is: the scrutinee at ",
        goto(ctx, info.taintedBy.start), " is tainted (", linked("§12"), ")."),
      info.topLevel ? muted("At the top level, every entry is global: see Global entries.")
        : info.scope.length ? h("div", { class: "scope" }, info.scope.map(e => scopeEntry(e, ctx)))
        : muted("No local entries.")),
    hidden(ctx, "Global entries", info.globalEntries.length, info.globalEntries.length
      ? h("div", { class: "scope" }, info.globalEntries.map(e => scopeEntry(e, ctx))) : muted("No global entries.")),
    ...refutations === null ? [] : [section("Refutations", list(refutations.map(r => {
      if (r.kind === "absurd") return h("li", {}, h("code", {}, r.ctor), " ", tag("absurd", true));
      return h("li", {}, dialog(h("code", {}, r.ctor), `Show why ${r.ctor} is refuted`,
        () => [h("h4", {}, "Why ", h("code", {}, r.ctor), " is refuted"), derivation(r.derivation, ctx)]));
    }), "No value constructor is refuted here."))],
  ];
}

const remembered = (ctx: Host, key: string, attrs: Record<string, string>, summary: Child, ...body: Child[]):
    HTMLElement =>
  h("details", { ...attrs, open: ctx.opened.has(key), ontoggle: (e: Event) => {
    if ((e.currentTarget as HTMLDetailsElement).open) ctx.opened.add(key); else ctx.opened.delete(key);
  } }, h("summary", {}, summary), body);

const hidden = (ctx: Host, title: string, count: number, ...body: Child[]): HTMLElement =>
  remembered(ctx, title, { class: "panel" }, `${title} (${count})`, ...body);

const declaration = (ctx: Host, g: { name: string; at: Span | null; signature: Rendered }): HTMLElement =>
  h("code", {}, h("span", { class: "name" }, g.at ? declaredAt(ctx, g.at, g.name) : g.name),
    rendered(g.signature, ctx));

const dataType = (ctx: Host, g: GlobalInfo): HTMLElement => h("li", { class: "global" }, g.ctors
  ? remembered(ctx, `data ${g.name}`, {}, declaration(ctx, g), g.ctors.length
    ? h("ul", {}, g.ctors.map(c => h("li", {}, declaration(ctx, c)))) : muted("No value constructors."))
  : declaration(ctx, g));

export const globalsView = (info: PositionInfo, ctx: Host): HTMLElement[] => {
  const of = (kind: GlobalInfo["kind"]) => info.globals.filter(g => g.kind === kind);
  return [
    hidden(ctx, "Data declarations", of("type").length,
      list(of("type").map(g => dataType(ctx, g)), "No data declarations.")),
    hidden(ctx, "Functions", of("fn").length, list(of("fn").map(g => h("li", { class: "global" },
      declaration(ctx, g))), "No functions.")),
  ];
};

const text = (r: Rendered | null): Child => r && unbroken(r.text);

export const entryTip = (e: EntryInfo, showErased: boolean): Child =>
  h("code", {}, typed(names(e), text(e.canonical.type.term), text(e.canonical.rule?.term ?? null),
    showErased && e.erased));

export const globalTip = (kind: string, name: string, signature: Rendered): Child =>
  globalLine(kind, name, text(signature));

export const explainTip = (r: Explained, showErased: boolean): Child => h("code", {}, "stands" in r
  ? ["(", r.stands.map((e, i) => [i > 0 && ", ", showErased && e.erased && "erased ",
    typed(e.name ?? "_", text(e.canonical.type?.term ?? null), text(e.canonical.rule?.term ?? null), false)]), ")"]
  : text(r.canonical));

export const inspectView = (info: PositionInfo, ctx: Host): HTMLElement => {
  const body = h("div", { class: "inspect-body" });
  return h("details", { class: "inspect",
    ontoggle: () => { if (!body.hasChildNodes()) body.append(...infoView(info, ctx), ...globalsView(info, ctx)); } },
    h("summary", {}, "inspect"), body);
};

const rewriteView = (r: Rewrite, ctx: Host): HTMLElement => {
  const by = ctx.entry(r.by);
  return h("li", {}, rendered(r.from, ctx), " → ", rendered(r.to, ctx), " ",
    muted("by "), goto(ctx, r.at.start, by?.names.join(", ") || ctx.at(r.at.start)));
};

export const explainView = (result: Explained | null, ctx: Host): Child =>
  result === null
    ? muted("No term at the caret.")
    : "stands" in result ? [h("p", {}, "Stands for"), expectedList(result.stands, ctx)]
    : [h("p", {}, "Canonical form: ", rendered(result.canonical, ctx)),
      result.rewrites.length ? h("ol", { class: "rewrites" }, result.rewrites.map(r => rewriteView(r, ctx)))
        : muted("Already canonical.")];

export const evalView = (result: ReturnType<CheckResult["evalAt"]>, ctx: Host): Child => {
  if ("error" in result) return h("p", { class: "bad" },
    `Column ${result.error.span.start + 1}: `, marked(result.error.message()));
  const rows = (term: string, inferred: Rendered | null, canonical: Rendered | null): Child =>
    [row(term, inferred ? rendered(inferred, ctx) : muted("no rule")),
      canonical && canonical.text !== inferred?.text && row("canonical", rendered(canonical, ctx))];
  return h("dl", {}, rows("type", result.type, result.canonicalType), rows("is", result.rule, result.canonicalRule));
};

export const verdict = (good: boolean | null, ...text: Child[]): HTMLElement =>
  h("span", { class: good === null ? "verdict" : good ? "verdict good" : "verdict bad" }, text);

const qedText: Record<CheckResult["qed"], string> = { none: "No qed", unreached: "qed not reached",
  fails: "qed does not check", checks: "qed checks" };

export const statusView = (r: Pick<CheckResult, "error" | "containsSorry" | "qed" | "goalProved">,
  error: string | null, qedMissing: boolean, ctx: Host): Child[] => {
  const proved = r.goalProved === null ? null : r.goalProved && !qedMissing;
  return [
    r.error ? verdict(false, "Error at ", goto(ctx, r.error.span.start), ": ", error && marked(error))
      : verdict(true, "No errors"),
    r.error?.derivation && derivation(r.error.derivation, ctx),
    h("span", { class: "verdicts" },
      verdict(!r.containsSorry, r.containsSorry ? "Contains sorry" : "No sorry"),
      qedMissing
        ? verdict(null, "No qed in your box")
        : verdict(r.qed === "checks" || (r.qed === "fails" ? false : null), qedText[r.qed]),
      verdict(proved, proved === null ? "No goal" : proved ? "Goal proved" : "Goal not proved")),
  ];
};
