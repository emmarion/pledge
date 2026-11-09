import type { EntryInfo, Rendered, Rewrite } from "./api.ts";
import { canon, entry, rewrites } from "./terms.ts";
import type { Binder, EntryId, OpenTerm, Scope, Signature, Telescope, Term } from "./terms.ts";

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

export function lineCol(source: string, offset: number): { line: number; col: number } {
  const lines = source.slice(0, offset).split("\n");
  return { line: lines.length, col: (lines.at(-1) ?? "").length + 1 };
}

export const position = (source: string) => (offset: number): string => {
  const { line, col } = lineCol(source, offset);
  return `${line}:${col}`;
};

export function label(scope: Scope, id: EntryId): string {
  const e = entry(scope, id);
  return e.names[0] ?? `?${e.origin.kind}@${scope.where(e.origin.span.start)}`;
}

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
  cat(b.mult === "erased" ? "erased " : "", b.name ?? "_", b.is ? " is " : " : ", render(scope, b.is ?? b.type, { canonical, bound }));

export function renderTelescope(scope: Scope, tele: Telescope, outer: readonly (string | null)[] = [], canonical = true): Rendered {
  const bound = [...outer, ...tele.map(b => b.name)];
  return cat("(", ...join(tele.map(b => renderBinder(scope, b, bound, canonical)), ", "), ")");
}

export const renderSignature = (scope: Scope, sig: Signature): Rendered =>
  cat(sig.head.name, renderTelescope(scope, sig.params), " : ", render(scope, sig.ret, { bound: sig.params.map(b => b.name) }));

export function entryInfo(scope: Scope, id: EntryId, canonical = true): EntryInfo {
  const e = entry(scope, id);
  return {
    id, names: [...e.names], origin: e.origin,
    type: render(scope, e.type, { canonical }),
    rule: e.rule && render(scope, e.rule.term, { canonical }),
    erased: e.erased, tainted: e.tainted,
  };
}

export function explain(scope: Scope, t: Term): { canonical: Rendered; rewrites: Rewrite[] } {
  const raw = (u: Term) => render(scope, u, { canonical: false });
  return { canonical: render(scope, t), rewrites: rewrites(scope, t).map(s => ({ from: raw(s.from), to: raw(s.to), by: s.by, at: s.at })) };
}
