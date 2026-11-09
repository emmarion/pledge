import type { Expr, Fn, Id, Pattern, Stmt } from "./syntax.ts";

export interface Value { head: string; args: Value[] }

export const removed: Value = Object.freeze({ head: "_", args: [] });

export type Env = ReadonlyMap<string, Value>;

export interface FnDef { fn: Fn; globals: Env }

export type Fns = ReadonlyMap<string, FnDef>;

export class InternalError extends Error {}

const fail = (message: string): never => { throw new InternalError(`internal error in the evaluator: ${message}`); };

const bind = (env: Env, ids: readonly Id[], vs: readonly Value[]): Env => {
  const out = new Map(env);
  ids.forEach((id, i) => { if (id.name !== null) out.set(id.name, vs[i] ?? fail(`no value for ${id.name}`)); });
  return out;
};

const take = (vs: Value[], n: number): Value[] =>
  vs.length === n ? vs
  : vs.length === 1 && vs[0] === removed ? Array<Value>(n).fill(removed)
  : fail(`expected ${n} values, got ${vs.length}`);

const tag = (v: Value): string => v === removed ? fail("a removed value was inspected") : v.head;

export const evalOne = (fns: Fns, env: Env, e: Expr): Value => take(evalExpr(fns, env, e), 1)[0]!;

export const bindPattern = (env: Env, pat: Pattern, v: Value): Env =>
  tag(v) === pat.ctor.name ? bind(env, pat.fields, v.args) : fail(`pattern ${pat.ctor.name} met ${showValue(v)}`);

export const evalExpr = (fns: Fns, env: Env, e: Expr): Value[] => {
  switch (e.kind) {
    case "var": return [env.get(e.name.name ?? "_") ?? fail(`unbound ${e.name.name}`)];
    case "app": {
      const args = e.args.map(a => evalOne(fns, env, a.expr));
      const def = fns.get(e.head.name ?? "_");
      if (!def) return [{ head: e.head.name ?? fail("application of _"), args }];
      const { fn, globals } = def;
      return take(evalExpr(fns, bind(globals, fn.params.map(p => p.name), args), fn.body), fn.returns.length);
    }
    case "tuple": return e.elems.map(x => evalOne(fns, env, x));
    case "block": return evalExpr(fns, e.stmts.reduce((acc, s) => evalStmt(fns, acc, s), env), e.final);
    case "match": {
      const v = evalOne(fns, env, e.scrut);
      const br = e.branches.find(b => b.pat.ctor.name === tag(v)) ?? fail(`no branch for ${showValue(v)}`);
      const vs = evalExpr(fns, bindPattern(env, br.pat, v), br.body);
      return e.ann === "_" ? vs : take(vs, e.ann.length);
    }
    case "sorry": return fail("sorry was reached");
    case "removed": return [removed];
  }
};

export const evalStmt = (fns: Fns, env: Env, s: Stmt): Env => {
  switch (s.kind) {
    case "let": return bind(env, s.binders.map(b => b.name), take(evalExpr(fns, env, s.rhs), s.binders.length));
    case "patlet": return bindPattern(env, s.pat, evalOne(fns, env, s.rhs));
    case "inspect": return env;
  }
};

export const showValue = (v: Value): string =>
  v === removed ? "_" : `${v.head}(${v.args.map(showValue).join(", ")})`;
