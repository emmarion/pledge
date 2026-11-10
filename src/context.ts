import type { Diagnostic, RefutationInfo, Rendered, TerminationInfo } from "./api.ts";
import type { Id, Phase, Span } from "./syntax.ts";
import { entry, lookup, mapLeaves } from "./terms.ts";
import type { Binder, EntryId, OpenTerm, Ref, Scope, Signature, Telescope, Term } from "./terms.ts";

export class Failure {
  readonly diag: Diagnostic;
  constructor(diag: Diagnostic) { this.diag = diag; }
}

export function fail(span: Span, message: () => string, derivation?: () => Rendered[]): never {
  throw new Failure({ span, message, ...(derivation ? { derivation } : {}) });
}

export function attempt<T>(f: () => T): T | { error: Diagnostic } {
  try {
    return f();
  } catch (e) {
    if (e instanceof Failure) return { error: e.diag };
    throw e;
  }
}

export interface FnSig { params: Telescope; returns: Telescope; subterm: readonly boolean[]; tainted: boolean }

export type Global =
  | { kind: "fn"; name: string; sig: FnSig | null }
  | { kind: "type"; name: string; sig: Signature; ctors: string[] | null; done: boolean }
  | { kind: "ctor"; name: string; sig: Signature }
  | { kind: "binding"; name: string; id: EntryId };

export type Want = Omit<Binder, "type"> & { type: OpenTerm | null };
export interface Given {
  wants: readonly Want[];
  env: readonly Ref[];
  whole: boolean;
  params?: number;
  label?: (i: number) => string;
}

export interface Local {
  scope: Scope;
  tainted: ReadonlySet<string>;
  erased: ReadonlySet<string>;
  taintedBy: Span | null;
}
export interface Result { id: EntryId; tainted: boolean; erased: boolean }

export interface FnCtx { name: string; group: readonly string[]; subterms: EntryId[]; info: TerminationInfo }

export interface Snapshot {
  span: Span;
  local: Local;
  given: Given | null;
  fn: FnCtx | null;
  refutations: RefutationInfo[] | null;
  limit: number;
  inspect: boolean;
  decl: EntryId | null;
}

interface ExplainPoint { span: Span; scope: Scope; of: Term | Given }

export type Declared = Exclude<Global, { kind: "binding" }>;
export interface Occurrence { span: Span; local: Local; of: EntryId | Declared }

export interface State {
  phase: Phase;
  globals: Global[];
  index: Map<string, number>;
  snapshots: Snapshot[];
  explains: ExplainPoint[];
  occurrences: Occurrence[];
  erased: Span[];
  record: boolean;
}

export interface Hole { id: EntryId; span: Span; is: Term | null; from: number; late: boolean }
export interface Ctx {
  st: State;
  fn: FnCtx | null;
  skeleton: boolean;
  limit: number | null;
  erased: boolean;
  inType: boolean;
  holes: Hole[];
  decl: EntryId | null;
}

export const APP = "app";
export const HOLE = "_";

const visible = (ctx: Ctx): number => ctx.limit ?? ctx.st.globals.length;

export function globalAt(st: State, limit: number, name: string): Global | undefined {
  const i = st.index.get(name);
  return i !== undefined && i < limit ? st.globals[i] : undefined;
}

export const global = (ctx: Ctx, name: string): Global | undefined => globalAt(ctx.st, visible(ctx), name);

export const code = (text: string | null): string => `\`${text ?? "_"}\``;

export const plural = (n: number, what: string): string => `${n} ${what}${n === 1 ? "" : "s"}`;

export const labelled = (role: string, name: string | null, i: number, owner?: string): string =>
  `${role} ${name === null ? i + 1 : code(name)}${owner === undefined ? "" : ` of ${code(owner)}`}`;

export function declareGlobal(st: State, g: Global): void {
  if (g.kind !== "binding") st.index.set(g.name, st.globals.length);
  st.globals.push(g);
}

export const describe = (g: Global): string =>
  g.kind === "fn" ? "a function" : g.kind === "type" ? "a type constructor" : g.kind === "ctor" ? "a value constructor"
    : "a value";

export function record(ctx: Ctx, local: Local, span: Span, given: Given | null, inspect = false): Snapshot {
  const snap: Snapshot = { span, local, given, fn: ctx.fn, refutations: null, limit: visible(ctx), inspect,
    decl: ctx.decl };
  if (ctx.st.record) ctx.st.snapshots.push(snap);
  return snap;
}

export function point(ctx: Ctx, scope: Scope, span: Span, of: Term | Given): void {
  if (ctx.st.record) ctx.st.explains.push({ span, scope, of });
}

export function occur(ctx: Ctx, span: Span, local: Local, of: EntryId | Declared): void {
  if (ctx.st.record) ctx.st.occurrences.push({ span, local, of });
}

export function erases(ctx: Ctx, span: Span): void {
  if (ctx.st.record && !ctx.erased) ctx.st.erased.push(span);
}

export const unfolds = (scope: Scope, id: EntryId): boolean => {
  const e = entry(scope, id);
  return e.rule !== null && (e.origin.kind === APP || e.origin.kind === HOLE) && !e.names.length;
};

export const written = (scope: Scope, t: Term): Term => mapLeaves(t, u =>
  unfolds(scope, u.id) ? written(scope, entry(scope, u.id).rule!.term) : u);

export function newName(ctx: Ctx, local: Local, id: Id, seen: Set<string>): void {
  const name = id.name;
  if (name === null) return;
  if (seen.has(name)) fail(id.span, () => `${code(name)} is introduced twice here (§2)`);
  if (lookup(local.scope, name) || global(ctx, name))
    fail(id.span, () => `${code(name)} is already in scope here, and no name is allowed to be shadowed (§2)`);
  seen.add(name);
}

export function innermost<T extends { span: Span }>(items: readonly T[], offset: number): T | undefined {
  let best: T | undefined;
  for (const x of items)
    if (x.span.start <= offset && offset <= x.span.end
      && (!best || x.span.end - x.span.start <= best.span.end - best.span.start)) best = x;
  return best;
}
