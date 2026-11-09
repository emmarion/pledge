import type { CheckResult, EntryId, EntryInfo, ExpectedEntry, Explained, PositionInfo, Rendered, Rewrite }
  from "../api.ts";
import { h, type Child } from "./dom.ts";
import { linked, marked, unbroken } from "./links.ts";

export interface Host {
  goto(offset: number): void;
  entry(id: EntryId): EntryInfo | undefined;
  where(offset: number): string;
  spot(offset: number): string;
  showErased: boolean;
  globalsOpen: boolean;
}

const muted = (text: string): HTMLElement => h("span", { class: "muted" }, text);

const link = (text: Child, title: string, onclick: () => void): HTMLElement =>
  h("button", { class: "link", type: "button", title, onclick }, text);

const goto = (ctx: Host, offset: number, text: Child = ctx.where(offset)): HTMLElement =>
  link(text, `Go to ${ctx.where(offset)}`, () => ctx.goto(offset));

function rendered(r: Rendered, ctx: Host): HTMLElement {
  const out = h("code", { class: "term" });
  let at = 0;
  for (const { span, entry } of [...r.refs].sort((a, b) => a.span.start - b.span.start)) {
    if (span.start < at) continue;
    const info = ctx.entry(entry);
    const text = unbroken(r.text.slice(span.start, span.end));
    out.append(...unbroken(r.text.slice(at, span.start)), ...info ? [link(text,
      `${info.origin.kind} at ${ctx.where(info.origin.span.start)}`, () => ctx.goto(info.origin.span.start))] : text);
    at = span.end;
  }
  out.append(...unbroken(r.text.slice(at)));
  return out;
}

const row = (term: string, value: Child): Child => [h("dt", {}, term), h("dd", {}, value)];

const tag = (text: string, show: boolean): Child => show && h("span", { class: "tag" }, text);

const typed = (name: Child, type: Child, rule: Child): Child =>
  [h("span", { class: "name" }, name), type && [" : ", type], rule && [" is ", rule]];

const binding = (ctx: Host, name: Child, type: Rendered | null, rule: Rendered | null, ...tags: Child[]): HTMLElement =>
  h("li", { class: "binding" }, typed(name, type && rendered(type, ctx), rule && rendered(rule, ctx)), tags);

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
  e.names.length ? names(e) : goto(ctx, e.origin.span.start,
    h("span", { class: "marker" }, `?${e.origin.kind}@${ctx.spot(e.origin.span.start)}`));

const expectedList = (entries: readonly ExpectedEntry[], ctx: Host): Child =>
  list(entries.map(e => binding(ctx, e.name ?? "_", e.type, e.rule, tag("erased", ctx.showErased && e.erased),
    tag("not determined", e.undetermined))), "none");

const derivation = (lines: () => Rendered[], ctx: Host): HTMLElement =>
  h("ol", { class: "derivation" }, lines().map(step => h("li", {}, rendered(step, ctx))));

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
    section("Scope",
      info.taintedBy && h("p", { class: "muted" }, "This scope is tainted, so every result here is: the scrutinee at ",
        goto(ctx, info.taintedBy.start), " is tainted (", linked("§12"), ")."),
      list(info.scope.map(e =>
        binding(ctx, entryName(e, ctx), e.type, e.rule, tag("erased", ctx.showErased && e.erased))),
        "No local entries.")),
    ...refutations === null ? [] : [section("Refutations", list(refutations.map(r => {
      if (r.kind === "absurd") return h("li", {}, h("code", {}, r.ctor), " ", tag("absurd", true));
      const steps = h("div", {});
      return h("li", {}, h("details", {
        ontoggle: () => { if (!steps.hasChildNodes()) steps.append(derivation(r.derivation, ctx)); },
      }, h("summary", {}, h("code", {}, r.ctor)), steps));
    }), "No value constructor is refuted here."))],
  ];
}

export const globalsView = (info: PositionInfo, ctx: Host): HTMLElement => h("details", {
  class: "panel globals", open: ctx.globalsOpen,
  ontoggle: (e: Event) => { ctx.globalsOpen = (e.currentTarget as HTMLDetailsElement).open; },
}, h("summary", {}, `Globals (${info.globals.length})`),
  list(info.globals.map(g => h("li", { class: "global" }, globalLine(g.kind, g.name, rendered(g.signature, ctx)),
    g.ctors && h("ul", {}, g.ctors.map(c => h("li", {}, signed(c.name, rendered(c.signature, ctx))))))),
    "No top-level names in scope."));

const text = (r: Rendered | null): Child => r && unbroken(r.text);

export const entryTip = (e: EntryInfo, showErased: boolean): Child =>
  [h("code", {}, typed(names(e), text(e.type), text(e.rule))), tag("erased", showErased && e.erased)];

export const globalTip = (kind: string, name: string, signature: Rendered): Child =>
  globalLine(kind, name, text(signature));

export const explainTip = (r: Explained, showErased: boolean): Child => h("code", {}, "stands" in r
  ? ["(", r.stands.map((e, i) => [i > 0 && ", ", showErased && e.erased && "erased ",
    typed(e.name ?? "_", text(e.type), text(e.rule))]), ")"]
  : text(r.canonical));

export const inspectView = (info: PositionInfo, ctx: Host): HTMLElement => {
  const body = h("div", { class: "inspect-body" });
  return h("details", { class: "inspect",
    ontoggle: () => { if (!body.hasChildNodes()) body.append(...infoView(info, ctx), globalsView(info, ctx)); } },
    h("summary", {}, "inspect"), body);
};

const rewriteView = (r: Rewrite, ctx: Host): HTMLElement => {
  const by = ctx.entry(r.by);
  return h("li", {}, rendered(r.from, ctx), " → ", rendered(r.to, ctx), " ",
    muted("by "), goto(ctx, r.at.start, by?.names.join(", ") || `the fact at ${ctx.where(r.at.start)}`));
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

export const statusView = (r: CheckResult, error: string | null, qedMissing: boolean, ctx: Host): Child[] => {
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
