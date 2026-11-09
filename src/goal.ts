import type { Expr, Span } from "./syntax.ts";
import type { Telescope, Term } from "./terms.ts";
import { difference } from "./telescope.ts";
import { renderBinder } from "./render.ts";
import { code, fail, global, occur, plural, record } from "./context.ts";
import type { Ctx, FnSig, Given, Global, Local } from "./context.ts";

type Telescopes = Pick<FnSig, "params" | "returns">;

export interface Goal { type: Term | Telescopes; tainted: boolean; span: Span }

export const goalGiven = (g: Goal): Given => "params" in g.type
  ? { wants: [...g.type.params, ...g.type.returns], env: [], whole: true, params: g.type.params.length }
  : { wants: [{ name: null, type: g.type, is: null, mult: "many", span: g.span }], env: [], whole: true };

const counts = (t: Telescopes): string =>
  `${plural(t.params.length, "parameter")} and ${plural(t.returns.length, "return")}`;

const named = (ctx: Ctx, e: Expr): Global | undefined => e.kind === "var" && e.name.name !== null
  ? global(ctx, e.name.name) : undefined;

export function qedFn(ctx: Ctx, top: Local, goal: Telescopes, e: Expr, given: Given): boolean {
  record(ctx, top, e.span, given);
  const f = named(ctx, e);
  if (f?.kind !== "fn" || !f.sig) return fail(e.span, () =>
    "the goal is a function goal, so `qed` names a function declared before it, as in `qed f;`");
  occur(ctx, e.span, top, f);
  const sig = f.sig, mine = [...sig.params, ...sig.returns], theirs = [...goal.params, ...goal.returns];
  if (sig.params.length !== goal.params.length || sig.returns.length !== goal.returns.length)
    fail(e.span, () => `${code(f.name)} has ${counts(sig)}, and the goal has ${counts(goal)}`);
  const i = difference(top.scope, theirs, mine), n = sig.params.length;
  const names = theirs.map(b => b.name), shown = (tele: Telescope) =>
    code(renderBinder(top.scope, { ...tele[i]!, name: names[i] ?? null }, names).text);
  if (i >= 0) fail(e.span, () =>
    `${code(f.name)}'s ${i < n ? `parameter ${i + 1}` : `return ${i - n + 1}`} is ${shown(mine)}, ` +
    `and the goal's is ${shown(theirs)} (binders named as in the goal); ` +
    "a function proves a function goal when its parameters and returns are canonically identical to the goal's, " +
    "position by position, binder names aside");
  return sig.tainted;
}

export function rejectFn(ctx: Ctx, top: Local, e: Expr, given: Given): void {
  const f = named(ctx, e);
  if (f?.kind !== "fn") return;
  record(ctx, top, e.span, given);
  fail(e.span, () => `${code(f.name)} is a function, and naming a function proves only a function goal, ` +
    "`goal fn (...) -> (...);`; this goal is a type");
}
