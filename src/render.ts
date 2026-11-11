import type { Canonical, EntryInfo, Rendered, Rewrite } from "./api.ts";
import type { Span } from "./syntax.ts";
import { canon, entries, entry, rewrites, signature } from "./terms.ts";
import { APP } from "./context.ts";
import type { Binder, Entry, EntryId, OpenTerm, Scope, Telescope } from "./terms.ts";

type Piece = string | Rendered;

export function cat(...pieces: readonly Piece[]): Rendered {
  let text = "";
  const refs: Rendered["refs"] = [];
  for (const p of pieces) {
    if (typeof p === "string") { text += p; continue; }
    const shift = text.length;
    refs.push(...p.refs.map(r => ({ ...r, span: { start: r.span.start + shift, end: r.span.end + shift } })));
    text += p.text;
  }
  return { text, refs };
}

export const join = (items: readonly Piece[], sep: string): Piece[] => items.flatMap((x, i) => i ? [sep, x] : [x]);

function marker(scope: Scope, { id, origin }: Entry): string {
  const at = origin.span.start, same = entries(scope).filter(e => !e.origin.blank && e.origin.span.start === at);
  const mark = origin.blank ? "_" : `?${same.length > 1 ? same.findIndex(e => e.id === id) + 1 : ""}`;
  return `${mark}@${scope.where(at)}`;
}

export const label = (scope: Scope, id: EntryId): string =>
  entry(scope, id).names[0] ?? marker(scope, entry(scope, id));

const whole = (text: string, to: { entry: EntryId } | { declared: Span }): Rendered =>
  ({ text, refs: [{ span: { start: 0, end: text.length }, ...to }] });

export const entryRef = (scope: Scope, id: EntryId): Rendered => whole(label(scope, id), { entry: id });

const headRef = (scope: Scope, name: string): Piece => {
  const at = signature(scope, name)?.at;
  return at ? whole(name, { declared: at }) : name;
};

interface RenderOptions { canonical?: boolean; bound?: readonly (string | null)[] }

export function render(scope: Scope, t: OpenTerm, opts: RenderOptions = {}): Rendered {
  const go = (u: OpenTerm): Rendered =>
    u.tag === "app" ? cat(headRef(scope, u.head.name), "(", ...join(u.args.map(go), ", "), ")")
      : u.tag === "entry" ? entryRef(scope, u.id)
      : cat(opts.bound?.[u.index] ?? `_${u.index + 1}`);
  return go(opts.canonical === false ? t : canon(scope, t));
}

export const renderBinder = (scope: Scope, b: Binder, bound: readonly (string | null)[], canonical = true): Rendered =>
  cat(b.mult === "erased" ? "erased " : "", b.name ?? "_", b.is ? " is " : " : ",
    render(scope, b.is ?? b.type, { canonical, bound }));

export function renderTelescope(scope: Scope, tele: Telescope, outer: readonly (string | null)[] = [],
    canonical = true): Rendered {
  const bound = [...outer, ...tele.map(b => b.name)];
  return cat("(", ...join(tele.map(b => renderBinder(scope, b, bound, canonical)), ", "), ")");
}

export const canonicalOf = (scope: Scope, t: OpenTerm, bound: readonly (string | null)[] = []): Canonical =>
  ({ term: render(scope, t, { bound }), rewrites: () => explain(scope, t, bound).rewrites });

export function entryInfo(scope: Scope, id: EntryId, canonical = true): EntryInfo {
  const e = entry(scope, id);
  return {
    id, names: [...e.names], origin: e.origin, marker: marker(scope, e),
    type: render(scope, e.type, { canonical }),
    rule: e.rule && render(scope, e.rule.term, { canonical }), ruleAt: e.rule?.at ?? null, typeAt: e.typeAt,
    canonical: { type: canonicalOf(scope, e.type), rule: e.rule && canonicalOf(scope, e.rule.term) },
    erased: e.erased, tainted: [],
  };
}

export function explain(scope: Scope, t: OpenTerm, bound: readonly (string | null)[] = []):
    { canonical: Rendered; rewrites: Rewrite[] } {
  const raw = (u: OpenTerm) => render(scope, u, { canonical: false, bound });
  return { canonical: render(scope, t, { bound }), rewrites: rewrites(scope, t).map(s => {
    const e = entry(scope, s.by), stated = (sep: string) => cat(entryRef(scope, s.by), sep, raw(e.rule!.term));
    return { from: raw(s.from), to: raw(s.to), by: s.by, at: s.at, rule: stated(" → "),
      how: () => e.rule!.how?.(scope) ?? [cat(stated(" is "), e.origin.kind === APP
        ? ": the entry of an application is that application (§7)" : ": the `is` clause of its binder (§6)")] };
  }) };
}
