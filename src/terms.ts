import type { Mult, Span } from "./syntax.ts";
import type { EntryId } from "./api.ts";

export type { EntryId };

export interface Head { kind: "type" | "ctor"; name: string }
export interface Ref { tag: "entry"; id: EntryId }
interface Bound { tag: "bound"; index: number }
export interface App<B = never> { tag: "app"; head: Head; args: readonly Term<B>[] }
export type Term<B = never> = Ref | App<B> | B;
export type OpenTerm = Term<Bound>;

export interface Binder { name: string | null; type: OpenTerm; is: OpenTerm | null; mult: Mult; span: Span }
export type Telescope = readonly Binder[];
export interface Signature { head: Head; params: Telescope; ret: OpenTerm }

export interface Origin { kind: string; span: Span }
interface Rule { term: Term; at: Span }
export interface Entry {
  readonly id: EntryId;
  readonly names: readonly string[];
  readonly type: Term;
  readonly rule: Rule | null;
  readonly origin: Origin;
  readonly erased: boolean;
  readonly tainted: boolean;
}
export interface Fresh { origin: Origin; erased?: boolean; tainted?: boolean }

type Key = string | number;
interface PNode<V> { readonly bucket: readonly (readonly [Key, V])[]; readonly l: PMap<V>; readonly r: PMap<V> }
type PMap<V> = PNode<V> | null;
interface Cons { readonly id: EntryId; readonly prev: Cons | null }

export interface Scope {
  readonly where: (offset: number) => string;
  readonly supply: { next: EntryId };
  readonly table: PMap<Entry>;
  readonly names: PMap<EntryId>;
  readonly sigs: PMap<Signature>;
  readonly order: Cons | null;
}

const hash = (k: Key): number =>
  typeof k === "number" ? k : [...k].reduce((h, c) => Math.imul(h ^ c.charCodeAt(0), 16777619) >>> 0, 2166136261);

function pget<V>(m: PMap<V>, k: Key): V | undefined {
  for (let h = hash(k); m && h; h >>>= 1) m = h & 1 ? m.r : m.l;
  return m?.bucket.find(([key]) => key === k)?.[1];
}

function pset<V>(m: PMap<V>, k: Key, v: V, h = hash(k)): PNode<V> {
  const n: PNode<V> = m ?? { bucket: [], l: null, r: null };
  if (h === 0) return { ...n, bucket: [...n.bucket.filter(([key]) => key !== k), [k, v]] };
  return h & 1 ? { ...n, r: pset(n.r, k, v, h >>> 1) } : { ...n, l: pset(n.l, k, v, h >>> 1) };
}

export const ref = (id: EntryId): Ref => ({ tag: "entry", id });
export const bound = (index: number): Bound => ({ tag: "bound", index });
export const app = <B = never>(head: Head, ...args: Term<B>[]): App<B> => ({ tag: "app", head, args });
export const TYPE: App = app({ kind: "type", name: "Type" });

export const declare = (scope: Scope, sig: Signature): Scope =>
  ({ ...scope, sigs: pset(scope.sigs, sig.head.name, sig) });
export const signature = (scope: Scope, name: string): Signature | undefined => pget(scope.sigs, name);

export const emptyScope = (where: (offset: number) => string): Scope =>
  declare({ where, supply: { next: 0 }, table: null, names: null, sigs: null, order: null },
    { head: TYPE.head, params: [], ret: TYPE });

export function entry(scope: Scope, id: EntryId): Entry {
  const e = pget(scope.table, id);
  if (!e) throw new Error(`internal: entry ${id} is not in this scope`);
  return e;
}

export function lookup(scope: Scope, name: string): Entry | undefined {
  const id = pget(scope.names, name);
  return id === undefined ? undefined : entry(scope, id);
}

export function entries(scope: Scope): Entry[] {
  const out: Entry[] = [];
  for (let c = scope.order; c; c = c.prev) out.push(entry(scope, c.id));
  return out.reverse();
}

const put = (scope: Scope, e: Entry): Scope => ({ ...scope, table: pset(scope.table, e.id, e) });

export function create(scope: Scope, type: Term, rule: Term | null, fresh: Fresh): { scope: Scope; id: EntryId } {
  const id = scope.supply.next++;
  const e: Entry = {
    id, names: [], type, rule: rule && { term: rule, at: fresh.origin.span }, origin: fresh.origin,
    erased: fresh.erased ?? false, tainted: fresh.tainted ?? false,
  };
  return { scope: { ...put(scope, e), order: { id, prev: scope.order } }, id };
}

export function withName(scope: Scope, id: EntryId, name: string): Scope {
  const e = entry(scope, id);
  return { ...put(scope, { ...e, names: [...e.names, name] }), names: pset(scope.names, name, id) };
}

export const forget = (inner: Scope, outer: Scope, named: readonly { name: string; id: EntryId }[]): Scope =>
  named.reduce((s, { name, id }) => put(s, { ...entry(s, id), names: entry(s, id).names.filter(n => n !== name) }),
    { ...inner, names: outer.names });

export const mark = (scope: Scope, id: EntryId, flags: { erased?: boolean; tainted?: boolean }): Scope =>
  put(scope, { ...entry(scope, id), ...flags });

export const addRule = (scope: Scope, id: EntryId, term: Term, at: Span): Scope =>
  put(scope, { ...entry(scope, id), rule: { term, at } });

export const mapLeaves = <B extends Bound, C extends Bound>(t: Term<B>, leaf: (u: Ref | B) => Term<C>): Term<C> =>
  t.tag === "app" ? { ...t, args: t.args.map(a => mapLeaves(a, leaf)) } : leaf(t);

export const subst = (t: OpenTerm, env: readonly Term[]): Term => mapLeaves(t, u => {
  if (u.tag === "entry") return u;
  const v = env[u.index];
  if (!v) throw new Error(`internal: bound variable ${u.index} outside its telescope`);
  return v;
});

export const abstract = (scope: Scope, t: Term, ids: readonly EntryId[]): OpenTerm => mapLeaves<never, Bound>(t, u => {
  const i = ids.indexOf(u.id), rule = entry(scope, u.id).rule;
  return i >= 0 ? bound(i) : rule ? abstract(scope, rule.term, ids) : u;
});

export function typeOf(scope: Scope, t: Term): Term {
  if (t.tag === "entry") return entry(scope, t.id).type;
  const sig = signature(scope, t.head.name);
  if (!sig) throw new Error(`internal: ${t.head.name} is not declared`);
  return subst(sig.ret, t.args);
}

export function canon(scope: Scope, t: Term): Term;
export function canon(scope: Scope, t: OpenTerm): OpenTerm;
export function canon(scope: Scope, t: OpenTerm): OpenTerm {
  return mapLeaves(t, u => {
    const rule = u.tag === "entry" && entry(scope, u.id).rule;
    return rule ? canon(scope, rule.term) : u;
  });
}

export const sameHead = (a: Head, b: Head): boolean => a.kind === b.kind && a.name === b.name;

export function same(a: OpenTerm, b: OpenTerm): boolean {
  if (a.tag === "app")
    return b.tag === "app" && sameHead(a.head, b.head) && a.args.length === b.args.length
      && a.args.every((x, i) => { const y = b.args[i]; return y !== undefined && same(x, y); });
  return a.tag === "entry" ? b.tag === "entry" && a.id === b.id : b.tag === "bound" && a.index === b.index;
}

export const identical = (scope: Scope, a: OpenTerm, b: OpenTerm): boolean => same(canon(scope, a), canon(scope, b));

export const mentions = (t: OpenTerm, which: (id: EntryId) => boolean): boolean =>
  t.tag === "app" ? t.args.some(a => mentions(a, which)) : t.tag === "entry" && which(t.id);

export const occurs = (id: EntryId, t: OpenTerm): boolean => mentions(t, x => x === id);

export function isStrictSubterm(scope: Scope, s: Term, t: Term): boolean {
  const cs = canon(scope, s);
  const below = (u: Term): boolean => u.tag === "app" && u.args.some(a => same(cs, a) || below(a));
  return below(canon(scope, t));
}

interface Step { by: EntryId; at: Span; from: Term; to: Term }

const replace = (t: Term, id: EntryId, by: Term): Term => mapLeaves(t, u => u.id === id ? by : u);

export function rewrites(scope: Scope, t: Term): Step[] {
  const seen = new Set<EntryId>(), post: [EntryId, Rule][] = [];
  const visit = (u: Term): void => {
    if (u.tag === "app") return u.args.forEach(visit);
    if (seen.has(u.id)) return;
    seen.add(u.id);
    const rule = entry(scope, u.id).rule;
    if (rule) { visit(rule.term); post.push([u.id, rule]); }
  };
  visit(t);
  const steps: Step[] = [];
  let from = t;
  for (const [by, rule] of post.reverse()) {
    const to = replace(from, by, rule.term);
    steps.push({ by, at: rule.at, from, to });
    from = to;
  }
  return steps;
}
