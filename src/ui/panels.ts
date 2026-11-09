import type { CheckResult, EntryId, EntryInfo, ExpectedEntry, PositionInfo, Rendered, Rewrite } from "../api.ts";
import { h, type Child } from "./dom.ts";

export interface Ctx {
  goto(offset: number): void;
  explain(offset: number): void;
  entry(id: EntryId): EntryInfo | undefined;
  where(offset: number): string;
  showErased: boolean;
  globalsOpen: boolean;
}

const muted = (text: string): HTMLElement => h("span", { class: "muted" }, text);

const link = (text: Child, title: string, onclick: () => void): HTMLElement =>
  h("button", { class: "link", type: "button", title, onclick }, text);

const goto = (ctx: Ctx, offset: number, text: Child = ctx.where(offset)): HTMLElement =>
  link(text, `Go to ${ctx.where(offset)}`, () => ctx.goto(offset));

function rendered(r: Rendered, ctx: Ctx): HTMLElement {
  const out = h("code", { class: "term" });
  let at = 0;
  for (const { span, entry } of [...r.refs].sort((a, b) => a.span.start - b.span.start)) {
    if (span.start < at) continue;
    const info = ctx.entry(entry);
    const text = r.text.slice(span.start, span.end);
    out.append(r.text.slice(at, span.start), info
      ? link(text, `${info.origin.kind} at ${ctx.where(info.origin.span.start)}`, () => {
        ctx.goto(info.origin.span.start);
        ctx.explain(info.origin.span.start);
      })
      : text);
    at = span.end;
  }
  out.append(r.text.slice(at));
  return out;
}

const row = (term: string, value: Child): Child => [h("dt", {}, term), h("dd", {}, value)];

const tag = (text: string, show: boolean): Child => show && h("span", { class: "tag" }, text);

const typed = (name: Child, type: Child, rule: Child): Child =>
  [h("span", { class: "name" }, name), type && [" : ", type], rule && [" is ", rule]];

const binding = (ctx: Ctx, name: Child, type: Rendered | null, rule: Rendered | null, ...tags: Child[]): HTMLElement =>
  h("li", { class: "binding" }, typed(name, type && rendered(type, ctx), rule && rendered(rule, ctx)), tags);

const signed = (name: string, signature: Child): HTMLElement => h("code", {}, h("span", { class: "name" }, name), signature);

const globalLine = (kind: string, name: string, signature: Child): Child => [h("span", { class: "kind" }, kind), " ", signed(name, signature)];

const section = (title: string, ...body: Child[]): HTMLElement =>
  h("section", { class: "panel" }, h("h3", {}, title), body);

const list = (items: Child[], empty: string): Child =>
  items.length ? h("ul", { class: "entries" }, items) : muted(empty);

const entryName = (e: EntryInfo, ctx: Ctx): Child =>
  e.names.length ? e.names.join(", ") : h("span", { class: "anon" }, `‹${e.origin.kind} `, goto(ctx, e.origin.span.start), "›");

const expectedList = (entries: readonly ExpectedEntry[], ctx: Ctx): Child =>
  list(entries.map(e => binding(ctx, e.name ?? "_", e.type, e.rule, tag("erased", ctx.showErased && e.erased), tag("not determined", e.undetermined))), "none");

export function infoView(info: PositionInfo, ctx: Ctx): HTMLElement[] {
  const { expected, termination, refutations } = info;
  return [
    section("Expected", expected?.entries == null
      ? muted("Nothing is given here.")
      : expected.params
        ? [h("p", {}, "A function with parameters"), expectedList(expected.params, ctx), h("p", {}, "and returns"), expectedList(expected.entries, ctx)]
        : expectedList(expected.entries, ctx)),
    section("Termination", termination === null
      ? muted("Not inside a function.")
      : h("dl", {},
        row("Function", h("code", {}, termination.fn)),
        row("subterm parameters", termination.subtermParams.length ? h("code", {}, termination.subtermParams.join(", ")) : muted("none")),
        row("Group", h("code", {}, termination.group.join(", "))))),
    section("Scope", list(info.scope.map(e =>
      binding(ctx, entryName(e, ctx), e.type, e.rule, tag("erased", ctx.showErased && e.erased))), "No local entries.")),
    ...refutations === null ? [] : [section("Refutations", list(refutations.map(r => {
      if (r.kind === "absurd") return h("li", {}, h("code", {}, r.ctor), " ", tag("absurd", true));
      const derivation = h("ol", { class: "derivation" });
      return h("li", {}, h("details", {
        ontoggle: () => { if (!derivation.hasChildNodes()) derivation.append(...r.derivation().map(step => h("li", {}, rendered(step, ctx)))); },
      }, h("summary", {}, h("code", {}, r.ctor)), derivation));
    }), "No value constructor is refuted here."))],
    h("details", {
      class: "panel globals", open: ctx.globalsOpen,
      ontoggle: (e: Event) => { ctx.globalsOpen = (e.currentTarget as HTMLDetailsElement).open; },
    }, h("summary", {}, `Globals (${info.globals.length})`),
      list(info.globals.map(g => h("li", { class: "global" }, globalLine(g.kind, g.name, rendered(g.signature, ctx)),
        g.ctors && h("ul", {}, g.ctors.map(c => h("li", {}, signed(c.name, rendered(c.signature, ctx))))))),
        "No top-level names in scope.")),
  ];
}

export const entryTip = (e: EntryInfo, showErased: boolean): Child =>
  [h("code", {}, typed(e.names.join(", "), e.type.text, e.rule?.text)), tag("erased", showErased && e.erased)];

export const globalTip = (kind: string, name: string, signature: Rendered): Child => globalLine(kind, name, signature.text);

export const inspectView = (info: PositionInfo, ctx: Ctx): HTMLElement => {
  const body = h("div", { class: "inspect-body" });
  return h("details", { class: "inspect", ontoggle: () => { if (!body.hasChildNodes()) body.append(...infoView(info, ctx)); } },
    h("summary", {}, "inspect"), body);
};

const rewriteView = (r: Rewrite, ctx: Ctx): HTMLElement => {
  const by = ctx.entry(r.by);
  return h("li", {}, rendered(r.from, ctx), " → ", rendered(r.to, ctx), " ",
    muted("by "), goto(ctx, r.at.start, by?.names.join(", ") || `the fact at ${ctx.where(r.at.start)}`));
};

export const explainView = (result: ReturnType<CheckResult["explainAt"]>, ctx: Ctx): Child =>
  result === null
    ? muted("No skeleton term here.")
    : [h("p", {}, "Canonical form: ", rendered(result.canonical, ctx)),
      result.rewrites.length ? h("ol", { class: "rewrites" }, result.rewrites.map(r => rewriteView(r, ctx))) : muted("Already canonical.")];

export const evalView = (result: ReturnType<CheckResult["evalAt"]>, ctx: Ctx): Child => {
  if ("error" in result) return h("p", { class: "bad" }, `Column ${result.error.span.start + 1}: ${result.error.message()}`);
  const rule = (r: Rendered | null): Child => r ? rendered(r, ctx) : muted("no rule");
  return h("dl", {}, row("Type", rendered(result.type, ctx)), row("canonical", rendered(result.canonicalType, ctx)),
    row("is", rule(result.rule)), row("canonical", rule(result.canonicalRule)));
};

export const verdict = (good: boolean | null, ...text: Child[]): HTMLElement =>
  h("span", { class: good === null ? "verdict" : good ? "verdict good" : "verdict bad" }, text);

export const statusView = (r: CheckResult, error: string | null, qedMissing: boolean, ctx: Ctx): Child[] => {
  const proved = r.goalProved === null ? null : r.goalProved && !qedMissing;
  return [
    r.error ? verdict(false, "Error at ", goto(ctx, r.error.span.start), ": ", error) : verdict(true, "No errors"),
    h("span", { class: "verdicts" },
      verdict(!r.containsSorry, r.containsSorry ? "Contains sorry" : "No sorry"),
      qedMissing
        ? verdict(null, "No qed in your box")
        : verdict(r.qedChecks, r.qedChecks === null ? "No qed" : r.qedChecks ? "qed checks" : "qed does not check"),
      verdict(proved, proved === null ? "No goal" : proved ? "Goal proved" : "Goal not proved")),
  ];
};
