import type { Expr, Fn, Id, Mult, Name, Pattern, Stmt } from "./syntax.ts";

export interface Value { head: string; args: Value[] }

export const removed: Value = Object.freeze({ head: "_", args: [] });

export type Env = ReadonlyMap<string, Value>;

export interface FnDef { fn: Fn; globals: Env }

export type Fns = ReadonlyMap<string, FnDef>;

const internal = (message: string): never => { throw new Error(`internal error in the evaluator: ${message}`); };

const bindValues = (env: Env, ids: readonly Id[], vs: readonly Value[]): Env => {
  const out = new Map(env);
  ids.forEach((id, i) => { if (id.name !== null) out.set(id.name, vs[i] ?? internal(`no value for ${id.name}`)); });
  return out;
};

const take = (vs: Value[], n: number): Value[] =>
  vs.length === n ? vs
  : vs.length === 1 && vs[0] === removed ? Array<Value>(n).fill(removed)
  : internal(`expected ${n} values, got ${vs.length}`);

const one = (vs: Value[]): Value => take(vs, 1)[0]!;

const tag = (v: Value): string => v === removed ? internal("a removed value was inspected") : v.head;

export const evalOne = (fns: Fns, env: Env, e: Expr): Value => one(evalExpr(fns, env, e));

export const bindPattern = (env: Env, pat: Pattern, v: Value, mult: Mult | null = null): Env =>
  mult === "erased" ? bindValues(env, pat.fields, pat.fields.map(() => removed))
  : tag(v) === pat.ctor.name ? bindValues(env, pat.fields, v.args)
    : internal(`pattern ${pat.ctor.name} met ${v.head}`);

const afterStmt = (env: Env, s: Stmt, vs: Value[]): Env =>
  s.kind === "let" ? bindValues(env, s.binders.map(b => b.name), take(vs, s.binders.length))
  : s.kind === "patlet" ? bindPattern(env, s.pat, one(vs), s.mult) : env;

type Block = Expr & { kind: "block" };
type Match = Expr & { kind: "match" };
type Step = Value[] | { expr: Expr; env: Env };
type Frame =
  | { kind: "take"; n: number }
  | { kind: "seq"; env: Env; exprs: readonly Expr[]; done: Value[]; head: Name | null }
  | { kind: "block"; env: Env; block: Block; i: number }
  | { kind: "match"; env: Env; match: Match };

export const evalExpr = (fns: Fns, env: Env, e: Expr): Value[] => {
  const stack: Frame[] = [];
  const returning = (n: number): void => {
    const top = stack.at(-1);
    if (top?.kind !== "take" || top.n !== n) stack.push({ kind: "take", n });
  };
  const seq = (env: Env, exprs: readonly Expr[], done: Value[], head: Name | null): Step => {
    const next = exprs[done.length];
    if (next) return stack.push({ kind: "seq", env, exprs, done, head }), { expr: next, env };
    if (!head) return done;
    const def = fns.get(head.name);
    if (!def) return [{ head: head.name, args: done }];
    returning(def.fn.returns.length);
    return { expr: def.fn.body, env: bindValues(def.globals, def.fn.params.map(p => p.name), done) };
  };
  const block = (env: Env, b: Block, i: number): Step => {
    const s = b.stmts[i];
    if (!s) return { expr: b.final, env };
    stack.push({ kind: "block", env, block: b, i });
    return s.kind === "inspect" ? [] : { expr: s.rhs, env };
  };
  const branch = (env: Env, m: Match, v: Value): Step => {
    const [only, ...others] = m.branches;
    const br = m.mult !== "erased" ? m.branches.find(b => b.pat.ctor.name === tag(v))
      ?? internal(`no branch for ${tag(v)}`)
      : only && !others.length ? only : internal(`an erased match with ${m.branches.length} branches`);
    if (Array.isArray(m.ann)) returning(m.ann.length);
    return { expr: br.body, env: bindPattern(env, br.pat, v, m.mult) };
  };
  const enter = (env: Env, e: Expr): Step => {
    switch (e.kind) {
      case "var": return [env.get(e.name.name ?? "_") ?? internal(`unbound ${e.name.name}`)];
      case "app": return seq(env, e.args.map(a => a.expr), [], e.head);
      case "tuple": return seq(env, e.elems, [], null);
      case "block": return block(env, e, 0);
      case "match": return stack.push({ kind: "match", env, match: e }), { expr: e.scrut, env };
      case "sorry": return internal("sorry was reached");
      case "removed": return [removed];
    }
  };
  const resume = (f: Frame, vs: Value[]): Step => {
    switch (f.kind) {
      case "take": return take(vs, f.n);
      case "seq": return seq(f.env, f.exprs, [...f.done, one(vs)], f.head);
      case "block": return block(afterStmt(f.env, f.block.stmts[f.i]!, vs), f.block, f.i + 1);
      case "match": return branch(f.env, f.match, one(vs));
    }
  };
  for (let step: Step = { expr: e, env };;) {
    if (!Array.isArray(step)) step = enter(step.env, step.expr);
    else {
      const f = stack.pop();
      if (!f) return step;
      step = resume(f, step);
    }
  }
};

export const evalStmt = (fns: Fns, env: Env, s: Stmt): Env =>
  afterStmt(env, s, s.kind === "inspect" ? [] : evalExpr(fns, env, s.rhs));

export const showValue = (v: Value): string => {
  const out: string[] = [];
  const todo: (Value | string)[] = [v];
  for (let x = todo.pop(); x !== undefined; x = todo.pop())
    if (typeof x === "string") out.push(x);
    else if (x === removed) out.push("_");
    else todo.push(")", ...x.args.flatMap((a, i) => i ? [", ", a] : [a]).reverse(), `${x.head}(`);
  return out.join("");
};
