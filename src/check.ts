import type { Check, CheckResult } from "./api.ts";
import type { Data, Expr, Fn, Name, Span, Top } from "./syntax.ts";
import { parse } from "./parser.ts";
import { hasKeyword } from "./lexer.ts";
import { TYPE, abstract, declare, emptyScope, ref, signature } from "./terms.ts";
import { position } from "./position.ts";
import { bindPattern, evalOne, evalStmt, showValue } from "./eval.ts";
import type { Env, FnDef, Value } from "./eval.ts";
import { Failure, attempt, code, declareGlobal, fail, labelled, newName, occur, record } from "./context.ts";
import type { Ctx, Declared, FnCtx, FnSig, Given, Global, Local, Snapshot, State } from "./context.ts";
import { annotate, closed, header, single, stmt, telescope, term } from "./expr.ts";
import { goalGiven, qedFn, rejectFn } from "./goal.ts";
import type { Goal } from "./goal.ts";
import { info, queries } from "./info.ts";

function run<T>(span: Span, f: () => T): T {
  try {
    return f();
  } catch (e) {
    if (e instanceof Failure) throw e;
    return fail(span, () => `evaluation stopped: ${e instanceof Error ? e.message : String(e)}`);
  }
}

const union = (spans: readonly Span[]): Span[] => [...spans].sort((a, b) => a.start - b.start)
  .reduce<Span[]>((out, s) => {
    const last = out.at(-1);
    return last && s.start <= last.end ? [...out.slice(0, -1), { start: last.start, end: Math.max(last.end, s.end) }]
      : [...out, s];
  }, []);

export const check: Check = (source, phase, where = position(source)) => {
  const { program: { tops }, error: syntax } = parse(source, phase);
  const has = (word: string): boolean => hasKeyword(source, phase, word);
  let top: Local = { scope: emptyScope(where), tainted: new Set(), erased: new Set(), taintedBy: null };
  const st: State = { phase, globals: [], index: new Map(), snapshots: [], explains: [], occurrences: [],
    erased: [], record: true };
  declareGlobal(st, { kind: "type", name: "Type", sig: signature(top.scope, "Type")!, ctors: null, done: true });
  const ctx: Ctx = { st, fn: null, skeleton: false, limit: null, erased: false, inType: false, holes: [], decl: null };
  const prints: CheckResult["prints"] = [], gaps: Snapshot[] = [];
  const fns = new Map<string, FnDef>();
  let env: Env = new Map(), proved = false, qedChecks = false;
  let goal: Goal | null = null;

  const inDecl = (): Ctx => ({ ...ctx, decl: top.scope.supply.next });
  const here = (span: Span, c = ctx): Snapshot => record(c, top, span, null);
  const declared = (c: Ctx, name: Name, g: Declared): void => {
    declareGlobal(st, g);
    occur(c, name.span, top, g);
  };

  const dataGroup = (c: Ctx, ds: readonly Data[]): void => {
    const types = ds.map(d => {
      here(d.span, c);
      newName(c, top, d.name, new Set());
      const name = d.name.name;
      const params = telescope(c, top, d.params, "binder").tele;
      const g: Global & { kind: "type" } = { kind: "type", name,
        sig: { head: { kind: "type", name }, params, ret: TYPE, retAt: d.span, at: d.name.span },
        ctors: [], done: false };
      top = { ...top, scope: declare(top.scope, g.sig) };
      declared(c, d.name, g);
      return g;
    });
    ds.forEach((d, i) => {
      const owner = types[i]!;
      for (const k of d.ctors) {
        here(k.span, c);
        newName(c, top, k.name, new Set());
        const name = k.name.name;
        const fields = telescope(c, top, k.fields, "binder");
        if (k.ret.head.name !== owner.name || k.ret.args === null)
          fail(k.ret.span, () =>
            `${code(name)} returns ${code(owner.name)} applied to one argument per parameter ` +
            `of ${code(owner.name)} (§5)`);
        const ret = term(c, fields.local, k.ret);
        const sig = { head: { kind: "ctor" as const, name }, params: fields.tele,
          ret: abstract(ret.local.scope, ref(ret.id), fields.ids), retAt: k.ret.span, at: k.name.span };
        top = { ...top, scope: declare(top.scope, sig) };
        declared(c, k.name, { kind: "ctor", name, sig });
        owner.ctors?.push(name);
      }
    });
    for (const g of types) g.done = true;
  };

  const fnGroup = (outer: Ctx, group: readonly Fn[]): void => {
    const names = group.map(f => f.name.name);
    const globals = group.map((f, i) => {
      newName(outer, top, f.name, new Set());
      const g: Global & { kind: "fn" } = { kind: "fn", name: names[i]!, sig: null, at: f.name.span };
      declared(outer, f.name, g);
      return g;
    });
    const heads = group.map((f, i) => {
      const name = names[i]!;
      const fn: FnCtx = { name, group: names, subterms: [],
        info: { fn: name, subtermParams: f.params.filter(p => p.subterm).map(p => p.name.name ?? "_"), group: names } };
      const c: Ctx = { ...outer, fn };
      record(c, top, f.span, null);
      const { params, returns } = header(c, top, f);
      fn.subterms.push(...params.ids.filter((_, j) => f.params[j]!.subterm));
      const sig: FnSig = { params: params.tele, returns: returns.tele, subterm: f.params.map(p => p.subterm),
        tainted: false };
      globals[i]!.sig = sig;
      return { f, c, sig, local: params.local, env: params.ids.map(ref) };
    });
    const logs = [st.snapshots, st.explains, st.occurrences, st.erased], marks = logs.map(log => log.length);
    for (;;) {
      logs.forEach((log, i) => { log.length = marks[i]!; });
      const bodies = heads.map((h, i) => closed(h.c, h.local, h.f.body, { wants: h.sig.returns, env: h.env, whole: true,
        label: j => labelled("return", h.sig.returns[j]?.name ?? null, j, names[i]) }));
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
    const out = closed(ctx, top, e, given), tainted = out.results.some(r => r.tainted);
    top = out.local;
    evaluated(span, out.tree, tainted);
    return tainted;
  };

  const evaluated = (span: Span, e: Expr, tainted: boolean): Value | null =>
    tainted ? null : run(span, () => evalOne(fns, env, e));

  const statement = (t: Top): void => {
    switch (t.kind) {
      case "data": return dataGroup(inDecl(), [t]);
      case "fn": return fnGroup(inDecl(), [t]);
      case "mutual": {
        const c = inDecl();
        here(t.span, c);
        return t.decls[0]?.kind === "data" ? dataGroup(c, t.decls as Data[]) : fnGroup(c, t.decls as Fn[]);
      }
      case "let": case "patlet": case "inspect": {
        const ran: { value: Value | null } = { value: null };
        const o = stmt(ctx, top, t, (tree, tainted) => {
          if (t.kind !== "patlet") return;
          const v = ran.value = evaluated(t.rhs.span, tree, tainted);
          if (v && v.head !== t.pat.ctor.name)
            fail(t.rhs.span, () =>
              `this evaluates to ${code(showValue(v))}, which is not headed by ${code(t.pat.ctor.name)} (§11)`);
        });
        for (const b of o.bound) declareGlobal(st, { kind: "binding", ...b });
        const v = ran.value;
        if (!o.local.taintedBy) env = t.kind === "patlet" && v ? bindPattern(env, t.pat, v)
          : run(t.span, () => evalStmt(fns, env, o.tree));
        top = o.local;
        return;
      }
      case "print": {
        here(t.span);
        const out = closed(ctx, top, t.expr, null, "the expression of a `print`");
        top = out.local;
        const v = evaluated(t.span, out.tree, single(out, t.expr.span).tainted);
        prints.push({ span: t.span, value: v ? showValue(v) : "sorry" });
        return;
      }
      case "goal": {
        const c = "params" in t.type ? inDecl() : ctx;
        here(t.span, c);
        if (goal) fail(t.span, () => "a program has at most one `goal` (§12)");
        if ("params" in t.type) {
          const { params, returns } = header(c, top, t.type);
          goal = { type: { params: params.tele, returns: returns.tele }, tainted: params.tainted || returns.tainted
            || top.taintedBy !== null, span: t.span };
          return;
        }
        const g = annotate(ctx, top, { kind: "type", term: t.type });
        top = g.local;
        goal = { type: g.type, tainted: g.tainted || top.taintedBy !== null, span: t.type.span };
        return;
      }
      case "qed": {
        here(t.span);
        if (qedChecks) fail(t.span, () => "a program has at most one `qed` (§12)");
        if (!goal) return fail(t.span, () => "`qed` comes after `goal`, and no `goal` is set before this `qed` (§12)");
        const tainted = "params" in goal.type ? qedFn(ctx, top, goal.type, t.expr, goalGiven(goal))
          : qedExpr(t.expr, goalGiven(goal), t.span);
        qedChecks = true;
        proved = !tainted && !top.taintedBy && !goal.tainted;
        return;
      }
    }
  };

  let last = 0, current = null as Top | null;
  const gap = (end: number) => { gaps.push(here({ start: last, end })); };
  const failed = attempt(() => {
    for (const t of tops) {
      gap(t.span.start);
      current = t;
      statement(t);
      last = t.span.end;
    }
    gap(source.length);
  })?.error ?? null;
  const error = failed ?? syntax;
  const fallback = (offset: number): Snapshot =>
    gaps.filter(g => g.span.start <= offset).at(-1) ?? gaps[0]
      ?? record({ ...ctx, st: { ...st, record: false } }, top, { start: 0, end: 0 }, null);
  return {
    phase, error, prints, erased: union(st.erased), containsSorry: has("sorry"),
    qed: !has("qed") ? "none" : failed && current?.kind === "qed" ? "fails" : qedChecks ? "checks" : "unreached",
    goalProved: has("goal") ? error === null && proved : null,
    inspects: st.snapshots.filter(s => s.inspect).map(s => ({ span: s.span, info: info(st, s) })),
    ...queries(st, fallback),
  };
};
