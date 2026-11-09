import type { Check, CheckResult, PositionInfo } from "./api.ts";
import type { Data, Expr, Fn, Span, Top } from "./syntax.ts";
import { parse } from "./parser.ts";
import { hasKeyword } from "./lexer.ts";
import { TYPE, abstract, declare, emptyScope, ref, signature } from "./terms.ts";
import { position } from "./position.ts";
import { bindPattern, evalOne, evalStmt, showValue } from "./eval.ts";
import type { Env, FnDef, Value } from "./eval.ts";
import { Failure, attempt, declareGlobal, fail, newName, record } from "./context.ts";
import type { Ctx, FnCtx, FnSig, Given, Global, Local, Snapshot, State } from "./context.ts";
import { annotate, expr, header, single, stmt, telescope, term } from "./expr.ts";
import { goalGiven, qedFn, rejectFn } from "./goal.ts";
import type { Goal } from "./goal.ts";
import { info, queries } from "./info.ts";

const nothing: PositionInfo = { expected: { entries: null }, termination: null, scope: [], refutations: null,
  globals: [] };

function run<T>(span: Span, f: () => T): T {
  try {
    return f();
  } catch (e) {
    if (e instanceof Failure) throw e;
    return fail(span, () => `evaluation stopped: ${e instanceof Error ? e.message : String(e)}`);
  }
}

export const check: Check = (source, phase, where = position(source)) => {
  const parsed = parse(source, phase);
  const containsSorry = hasKeyword(source, phase, "sorry");
  if ("error" in parsed)
    return {
      phase, error: parsed.error, containsSorry, qedChecks: null, goalProved: null, prints: [], inspects: [],
      infoAt: () => nothing, explainAt: () => null, evalAt: () => ({ error: parsed.error }),
    };
  const { tops } = parsed.program;
  let top: Local = { scope: emptyScope(where), tainted: new Set(), erased: new Set(), allTainted: false };
  const st: State = { phase, globals: [], index: new Map(), snapshots: [], explains: [], record: true };
  declareGlobal(st, { kind: "type", name: "Type", sig: signature(top.scope, "Type")!, ctors: null, done: true });
  const ctx: Ctx = { st, fn: null, skeleton: false, limit: null, erased: false, holes: [] };
  const prints: CheckResult["prints"] = [], gaps: Snapshot[] = [];
  const fns = new Map<string, FnDef>();
  let env: Env = new Map(), proved = false;
  let goal: Goal | null = null;
  const hasQed = tops.some(t => t.kind === "qed");
  let qedChecks: boolean | null = hasQed ? false : null, qedSeen = false;

  const here = (span: Span, given: Given | null = null): Snapshot => record(ctx, top, span, given);

  const dataGroup = (ds: readonly Data[]): void => {
    const types = ds.map(d => {
      here(d.span);
      newName(ctx, top, d.name, new Set());
      const name = d.name.name ?? "_";
      const params = telescope(ctx, top, d.params, "binder").tele;
      const g: Global & { kind: "type" } = { kind: "type", name,
        sig: { head: { kind: "type", name }, params, ret: TYPE }, ctors: [], done: false };
      top = { ...top, scope: declare(top.scope, g.sig) };
      declareGlobal(st, g);
      return g;
    });
    ds.forEach((d, i) => {
      const owner = types[i]!;
      for (const c of d.ctors) {
        here(c.span);
        newName(ctx, top, c.name, new Set());
        const name = c.name.name ?? "_";
        const fields = telescope(ctx, top, c.fields, "binder");
        if (c.ret.head.name !== owner.name || c.ret.args === null)
          fail(c.ret.span, () =>
            `${name} returns ${owner.name} applied to one argument per parameter of ${owner.name} (§5)`);
        const ret = term(ctx, fields.local, c.ret);
        const sig = { head: { kind: "ctor" as const, name }, params: fields.tele,
          ret: abstract(ret.local.scope, ref(ret.id), fields.ids) };
        top = { ...top, scope: declare(top.scope, sig) };
        declareGlobal(st, { kind: "ctor", name, sig });
        owner.ctors?.push(name);
      }
    });
    for (const g of types) g.done = true;
  };

  const fnGroup = (group: readonly Fn[]): void => {
    const names = group.map(f => f.name.name ?? "_");
    const globals = group.map((f, i) => {
      newName(ctx, top, f.name, new Set());
      const g: Global & { kind: "fn" } = { kind: "fn", name: names[i]!, sig: null };
      declareGlobal(st, g);
      return g;
    });
    const heads = group.map((f, i) => {
      const name = names[i]!;
      const fn: FnCtx = { name, group: names, subterms: [],
        info: { fn: name, subtermParams: f.params.filter(p => p.subterm).map(p => p.name.name ?? "_"), group: names } };
      const c: Ctx = { ...ctx, fn };
      record(c, top, f.span, null);
      const { params, returns } = header(c, { ...top, allTainted: false }, f);
      fn.subterms.push(...params.ids.filter((_, j) => f.params[j]!.subterm));
      const sig: FnSig = { params: params.tele, returns: returns.tele, subterm: f.params.map(p => p.subterm),
        tainted: false };
      globals[i]!.sig = sig;
      return { f, c, sig, local: params.local, env: params.ids.map(ref) };
    });
    const marks = [st.snapshots.length, st.explains.length] as const;
    for (;;) {
      st.snapshots.length = marks[0];
      st.explains.length = marks[1];
      const bodies = heads.map(h => expr(h.c, h.local, h.f.body, { wants: h.sig.returns, env: h.env, whole: true }));
      const now = bodies.map(b => b.results.some(r => r.tainted));
      if (!now.some((t, i) => t && !heads[i]!.sig.tainted)) {
        heads.forEach((h, i) => {
          const tree = bodies[i]!.tree;
          fns.set(names[i]!, { fn: { ...h.f, body: tree.kind === "block" ? tree
            : { kind: "block", stmts: [], final: tree, span: tree.span } }, globals: env });
        });
        return;
      }
      now.forEach((t, i) => { heads[i]!.sig.tainted ||= t; });
    }
  };

  const qedExpr = (e: Expr, given: Given, span: Span): boolean => {
    rejectFn(ctx, top, e, given);
    const out = expr(ctx, top, e, given), tainted = out.results.some(r => r.tainted);
    top = out.local;
    evaluated(span, out.tree, tainted);
    return tainted;
  };

  const evaluated = (span: Span, e: Expr, tainted: boolean): Value | null =>
    tainted ? null : run(span, () => evalOne(fns, env, e));

  const statement = (t: Top): void => {
    switch (t.kind) {
      case "data": return dataGroup([t]);
      case "fn": return fnGroup([t]);
      case "mutual":
        here(t.span);
        return t.decls[0]?.kind === "data" ? dataGroup(t.decls as Data[]) : fnGroup(t.decls as Fn[]);
      case "let": case "patlet": case "inspect": {
        const ran: { value: Value | null } = { value: null };
        const o = stmt(ctx, top, t, (tree, tainted) => {
          if (t.kind !== "patlet") return;
          const v = ran.value = evaluated(t.rhs.span, tree, tainted);
          if (v && v.head !== t.pat.ctor.name)
            fail(t.rhs.span, () =>
              `this evaluates to ${showValue(v)}, which is not headed by ${t.pat.ctor.name} (§11)`);
        });
        for (const b of o.bound) declareGlobal(st, { kind: "binding", ...b });
        const v = ran.value;
        if (!o.local.allTainted) env = t.kind === "patlet" && v ? bindPattern(env, t.pat, v)
          : run(t.span, () => evalStmt(fns, env, o.tree));
        top = o.local;
        return;
      }
      case "print": {
        here(t.span);
        const out = expr(ctx, top, t.expr, null);
        top = out.local;
        const v = evaluated(t.span, out.tree, single(out, t.expr.span).tainted);
        prints.push({ span: t.span, value: v ? showValue(v) : "sorry" });
        return;
      }
      case "goal": {
        here(t.span);
        if (goal) fail(t.span, () => "a program has at most one `goal` (§12)");
        if ("params" in t.type) {
          const { params, returns } = header(ctx, top, t.type);
          goal = { type: { params: params.tele, returns: returns.tele }, tainted: params.tainted || returns.tainted
            || top.allTainted, span: t.span };
          return;
        }
        const g = annotate(ctx, top, { kind: "type", term: t.type });
        top = g.local;
        goal = { type: g.type, tainted: g.tainted || top.allTainted, span: t.type.span };
        return;
      }
      case "qed": {
        here(t.span);
        if (qedSeen) fail(t.span, () => "a program has at most one `qed` (§12)");
        qedSeen = true;
        if (!goal) return fail(t.span, () => "`qed` comes after `goal`, and no `goal` is set before this `qed` (§12)");
        const tainted = "params" in goal.type ? qedFn(ctx, top, goal.type, t.expr, goalGiven(goal))
          : qedExpr(t.expr, goalGiven(goal), t.span);
        qedChecks = true;
        proved = !tainted && !top.allTainted && !goal.tainted;
        return;
      }
    }
  };

  let last = 0;
  const gap = (end: number) => { gaps.push(here({ start: last, end })); };
  const error = attempt(() => {
    for (const t of tops) {
      gap(t.span.start);
      statement(t);
      last = t.span.end;
    }
    gap(source.length);
  })?.error ?? null;
  const fallback = (offset: number): Snapshot =>
    gaps.filter(g => g.span.start <= offset).at(-1) ?? gaps[0]
      ?? record({ ...ctx, st: { ...st, record: false } }, top, { start: 0, end: 0 }, null);
  return {
    phase, error, qedChecks, prints, containsSorry,
    goalProved: tops.some(t => t.kind === "goal") ? error === null && proved : null,
    inspects: st.snapshots.filter(s => s.inspect).map(s => ({ span: s.span, info: info(st, s) })),
    ...queries(st, fallback),
  };
};
