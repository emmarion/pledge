import type { Diagnostic, RefutationInfo, TerminationInfo } from "./api.ts";
import type { Id, Mult, Phase, Span } from "./syntax.ts";
import { entry, lookup } from "./terms.ts";
import type { EntryId, OpenTerm, Scope, Signature, Telescope, Term } from "./terms.ts";

export class Failure {
  readonly diag: Diagnostic;
  constructor(diag: Diagnostic) { this.diag = diag; }
}

export function fail(span: Span, message: () => string): never {
  throw new Failure({ span, message });
}

export interface FnSig { params: Telescope; returns: Telescope; subterm: readonly boolean[]; tainted: boolean }

export type Global =
  | { kind: "fn"; name: string; sig: FnSig | null }
  | { kind: "type"; name: string; sig: Signature; ctors: string[] | null; done: boolean }
  | { kind: "ctor"; name: string; sig: Signature }
  | { kind: "binding"; name: string; id: EntryId };

export interface Want { name: string | null; type: OpenTerm | null; is: OpenTerm | null; mult: Mult; span: Span }
export interface Given { wants: readonly Want[]; env: readonly Term[]; whole: boolean }

export interface Local { scope: Scope; tainted: ReadonlySet<string> }
export interface Result { id: EntryId; tainted: boolean }

export interface FnCtx { name: string; group: readonly string[]; subterms: EntryId[]; info: TerminationInfo }

export interface Snapshot {
  span: Span;
  local: Local;
  given: Given | null | "none";
  fn: FnCtx | null;
  refutations: RefutationInfo[] | null;
  limit: number;
  inspect: boolean;
}

export interface ExplainPoint { span: Span; scope: Scope; term: Term }

export interface State {
  phase: Phase;
  globals: Global[];
  index: Map<string, number>;
  snapshots: Snapshot[];
  explains: ExplainPoint[];
  record: boolean;
}

export interface Ctx { st: State; fn: FnCtx | null; skeleton: boolean; limit: number | null }

export const APP = "app";

export const visible = (ctx: Ctx): number => ctx.limit ?? ctx.st.globals.length;

export function global(ctx: Ctx, name: string): Global | undefined {
  const i = ctx.st.index.get(name);
  return i !== undefined && i < visible(ctx) ? ctx.st.globals[i] : undefined;
}

export function declareGlobal(st: State, g: Global): void {
  if (g.kind !== "binding") st.index.set(g.name, st.globals.length);
  st.globals.push(g);
}

export const describe = (g: Global): string =>
  g.kind === "fn" ? "a function" : g.kind === "type" ? "a type constructor" : g.kind === "ctor" ? "a value constructor" : "a value";

export function record(ctx: Ctx, local: Local, span: Span, given: Given | null | "none", inspect = false): Snapshot {
  const snap: Snapshot = { span, local, given, fn: ctx.fn, refutations: null, limit: visible(ctx), inspect };
  if (ctx.st.record) ctx.st.snapshots.push(snap);
  return snap;
}

export function point(ctx: Ctx, scope: Scope, span: Span, term: Term): void {
  if (ctx.st.record) ctx.st.explains.push({ span, scope, term });
}

export function written(scope: Scope, t: Term): Term {
  if (t.tag === "app") return { ...t, args: t.args.map(a => written(scope, a)) };
  const e = entry(scope, t.id);
  return e.rule && e.origin.kind === APP && !e.names.length ? written(scope, e.rule.term) : t;
}

export function fresh(ctx: Ctx, local: Local, id: Id, seen: Set<string>): void {
  const name = id.name;
  if (name === null) return;
  if (seen.has(name)) fail(id.span, () => `${name} is introduced twice here (§2)`);
  if (lookup(local.scope, name) || global(ctx, name))
    fail(id.span, () => `${name} is already in scope here, and no name is allowed to be shadowed (§2)`);
  seen.add(name);
}

export function innermost<T extends { span: Span }>(items: readonly T[], offset: number): T | undefined {
  let best: T | undefined;
  for (const x of items)
    if (x.span.start <= offset && offset <= x.span.end && (!best || x.span.end - x.span.start <= best.span.end - best.span.start)) best = x;
  return best;
}
