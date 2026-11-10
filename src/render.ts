import type { EntryInfo, Rendered, Rewrite } from "./api.ts";
import { canon, entry, rewrites } from "./terms.ts";
import type { Binder, Entry, EntryId, OpenTerm, Scope, Telescope, Term } from "./terms.ts";

type Piece = string | Rendered;

export function cat(...pieces: readonly Piece[]): Rendered {
  let text = "";
  const refs: Rendered["refs"] = [];
  for (const p of pieces) {
    if (typeof p === "string") { text += p; continue; }
    const shift = text.length;
    refs.push(...p.refs.map(r => ({ entry: r.entry, span: { start: r.span.start + shift, end: r.span.end + shift } })));
    text += p.text;
  }
  return { text, refs };
}

export const join = (items: readonly Piece[], sep: string): Piece[] => items.flatMap((x, i) => i ? [sep, x] : [x]);

const marker = (scope: Scope, { origin }: Entry): string =>
  `${origin.blank ? "_" : `?${origin.kind}`}@${scope.where(origin.span.start)}`;

export const label = (scope: Scope, id: EntryId): string =>
  entry(scope, id).names[0] ?? marker(scope, entry(scope, id));

export function entryRef(scope: Scope, id: EntryId): Rendered {
  const text = label(scope, id);
  return { text, refs: [{ span: { start: 0, end: text.length }, entry: id }] };
}

interface RenderOptions { canonical?: boolean; bound?: readonly (string | null)[] }

export function render(scope: Scope, t: OpenTerm, opts: RenderOptions = {}): Rendered {
  const go = (u: OpenTerm): Rendered =>
    u.tag === "app" ? cat(u.head.name, "(", ...join(u.args.map(go), ", "), ")")
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

export function entryInfo(scope: Scope, id: EntryId, canonical = true): EntryInfo {
  const e = entry(scope, id);
  return {
    id, names: [...e.names], origin: e.origin, marker: marker(scope, e),
    type: render(scope, e.type, { canonical }),
    rule: e.rule && render(scope, e.rule.term, { canonical }),
    erased: e.erased, tainted: [],
  };
}

export function explain(scope: Scope, t: Term): { canonical: Rendered; rewrites: Rewrite[] } {
  const raw = (u: Term) => render(scope, u, { canonical: false });
  return { canonical: render(scope, t), rewrites: rewrites(scope, t).map(s =>
    ({ from: raw(s.from), to: raw(s.to), by: s.by, at: s.at })) };
}
