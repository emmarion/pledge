import type { Ann, Arg, Expr, Header, Id, LetBinder, Mult, Name, Pattern, Span, Stmt, Tele, WrittenBinder,
  WrittenTerm } from "./syntax.ts";
import { TYPE, abstract, addRule, app, blank, canon, create, entry, forget, identical, isStrictSubterm, known, lookup,
  mapLeaves, mark, mentions, occurs, ref, subst, typeOf, withName } from "./terms.ts";
import type { Binder, EntryId, Ref, Scope, Signature, Telescope, Term } from "./terms.ts";
import { force, open, unify } from "./telescope.ts";
import type { Forced } from "./telescope.ts";
import { label, render } from "./render.ts";
import type { RefutationInfo } from "./api.ts";
import { APP, HOLE, code, describe, erases, fail, labelled, newName, global, occur, plural, point, record, unfolds,
  written } from "./context.ts";
import type { Ctx, FnCtx, FnSig, Given, Global, Hole, Local, Result, Snapshot, Want } from "./context.ts";

type App = Expr & { kind: "app" };
type Match = Expr & { kind: "match" };
interface Out { local: Local; results: Result[]; tree: Expr }
interface Named { name: string; id: EntryId }
interface StmtOut { local: Local; tree: Stmt; bound: Named[] }
type Comptime = (tree: Expr, tainted: boolean) => void;
interface Forcing { name: string; forced: Forced; pat: Pattern | undefined }

const show = (scope: Scope, t: Term): string => code(render(scope, t).text);
const spelled = (scope: Scope, t: Term): Term => mapLeaves(t, u =>
  unfolds(scope, u.id) && entry(scope, u.id).origin.kind !== HOLE ? spelled(scope, entry(scope, u.id).rule!.term) : u);
const trees = (scope: Scope, results: readonly Result[]): Term[] => results.map(r => spelled(scope, ref(r.id)));
const are = (n: number, what: string): string => `${plural(n, what)} ${n === 1 ? "is" : "are"}`;
const miscount = (span: Span, want: number, got: string): never =>
  fail(span, () => `${are(want, "value")} expected here, and this ${got} (§8)`);

export function single(out: Out, span: Span): Result {
  const [r] = out.results;
  return r && out.results.length === 1 ? r : miscount(span, 1, `produces ${out.results.length}`);
}

const reach = (local: Local, scrutinee: Result, span: Span): Span | null =>
  local.taintedBy ?? (scrutinee.tainted ? span : null);

const erasedAt = (given: Given | null, i: number): boolean => given?.wants[i]?.mult === "erased";
const erase = (given: Given): Given => ({ ...given, wants: given.wants.map(w => ({ ...w, mult: "erased" as const })) });

const ELSEWHERE = "this position";

export function expr(ctx: Ctx, local: Local, e: Expr, given: Given | null, where = ELSEWHERE): Out {
  const whole = ctx.erased || (given !== null && given.wants.every(w => w.mult === "erased"));
  const g = ctx.erased && given ? erase(given) : given, c = whole === ctx.erased ? ctx : { ...ctx, erased: whole };
  if (whole) erases(ctx, e.span);
  const built = build(c, local, e, g, record(c, local, e.span, g), where);
  const out = built.local.taintedBy ? { ...built, results: built.results.map(r => ({ ...r, tainted: true })) } : built;
  const leak = whole ? -1 : out.results.findIndex((r, i) => r.erased && !erasedAt(g, i));
  if (leak >= 0) fail(e.span, () =>
    (e.kind === "var" ? code(e.name.name) : out.results.length === 1 ? "this value" : `value ${leak + 1} of this`) +
    ` is erased, and ${g?.label?.(leak) ?? (g ? ELSEWHERE : where)} is not; ` +
    "an erased value is allowed only in an erased position: a type, " +
    "an argument for an erased parameter or field, or the result for an erased return or binder (§16)");
  return whole || out.results.every(r => r.tainted) ? { ...out, tree: { kind: "removed", span: e.span } } : out;
}

function produced(ctx: Ctx, local: Local, given: Given | null, results: Result[], span: Span, tree: Expr): Out {
  return { local: given ? { ...local, scope: against(ctx, local.scope, given, results.map(r => r.id), span) } : local,
    results, tree };
}

const wanted = (given: Given, ids: readonly EntryId[], i: number): { type: Term | null; is: Term | null } => {
  const w = given.wants[i]!, env = [...given.env, ...ids.slice(0, i).map(ref)];
  return { type: w.type && subst(w.type, env), is: w.is && subst(w.is, env) };
};

function solveHoles(ctx: Ctx, scope: Scope, lhs: Term, rhs: Term, at: Span): Scope {
  if (!ctx.holes.length) return scope;
  const { scope: now, stuck } = unify(scope, lhs, rhs, at, id => ctx.holes.some(h => h.id === id));
  const hole = stuck && ctx.holes.find(h => stuck.some(t => occurs(h.id, t)));
  if (stuck && hole) fail(hole.span, () =>
    `this \`_\` cannot be inferred: it would need ${show(now, stuck[0])} and ${show(now, stuck[1])} to be equal, ` +
    "and this checker solves a `_` only by giving a rule to its own entry");
  return now;
}

function against(ctx: Ctx, before: Scope, given: Given, ids: readonly EntryId[], span: Span): Scope {
  const n = given.wants.length;
  if (ids.length !== n) miscount(span, n, `produces ${ids.length}`);
  return given.wants.reduce((acc, w, i) => {
    const id = ids[i]!, { type, is } = wanted(given, ids, i);
    const what = () => given.label?.(i) ?? (w.name !== null ? code(w.name) : n === 1 ? "the value expected here"
      : `value ${i + 1}`);
    const withType = type ? solveHoles(ctx, acc, type, entry(acc, id).type, span) : acc;
    const scope = is ? solveHoles(ctx, withType, is, ref(id), span) : withType;
    if (type && !identical(scope, type, entry(scope, id).type))
      fail(span, () =>
        `${what()} must have type ${show(scope, type)}, and this has type ${show(scope, entry(scope, id).type)}`);
    if (is && !identical(scope, is, ref(id)))
      fail(span, () => `${what()} must be ${show(scope, is)}, and this is ${show(scope, ref(id))}`);
    return scope;
  }, before);
}

function settle(ctx: Ctx, scope: Scope, since: number): ReadonlySet<EntryId> {
  const unsolved = (x: EntryId): boolean => entry(scope, x).origin.kind === HOLE && !entry(scope, x).rule;
  const bad = new Set<EntryId>();
  for (const { id, span, is, from, late } of ctx.holes.splice(since)) {
    const value = canon(scope, ref(id)), type = entry(scope, id).type;
    point(ctx, scope, span, ref(id));
    if (mentions(value, unsolved)) fail(span, () =>
      "this `_` cannot be inferred: a `_` is solved only by unification, from the arguments around it " +
      "and what its position is given, before the call, statement, scrutinee, body or binder it is in ends, " +
      "and these do not determine it (§16)");
    if (!late && mentions(value, x => x > id)) fail(span, () =>
      `this \`_\` would be ${show(scope, value)}, which mentions what is produced only after it, ` +
      "such as a result of the call it is an argument of, and a `_` is solved only to what exists before it");
    const has = typeOf(scope, value);
    if (!identical(scope, type, has)) fail(span, () =>
      `this \`_\` would be ${show(scope, value)}, of type ${show(scope, has)}, ` +
      `and it must have type ${show(scope, type)}`);
    if (is && !identical(scope, is, value)) fail(span, () =>
      `this \`_\` must be ${show(scope, is)}, and it would be ${show(scope, value)}`);
    for (const p of ctx.st.explains.slice(from))
      if (!mentions(value, x => !known(p.scope, x)) && !entry(p.scope, id).rule)
        p.scope = addRule(p.scope, id, value, span);
    if (mentions(value, x => entry(scope, x).tainted)) bad.add(id);
  }
  return bad;
}

function close(ctx: Ctx, out: Out, since: number, all = false): Out {
  const bad = settle(ctx, out.local.scope, since);
  if (!bad.size) return out;
  const before = out.local.scope;
  const via = (t: Term): boolean => t.tag === "app" ? t.args.some(via)
    : bad.has(t.id) || unfolds(before, t.id) && via(entry(before, t.id).rule!.term);
  const results = out.results.map(r => all || via(ref(r.id)) ? { ...r, tainted: true } : r);
  const scope = results.reduce((acc, r) => r.tainted ? mark(acc, r.id, { tainted: true }) : acc, before);
  return { local: { ...out.local, scope }, results,
    tree: results.every(r => r.tainted) ? { kind: "removed", span: out.tree.span } : out.tree };
}

export function closed(ctx: Ctx, local: Local, e: Expr, given: Given | null, where = ELSEWHERE): Out {
  const c = { ...ctx, holes: [] };
  return close(c, expr(c, local, e, given, where), 0);
}

function hole(ctx: Ctx, local: Local, span: Span, type: Term, is: Term | null,
    erased: boolean): { local: Local; result: Result } {
  const made = create(local.scope, type, null, { origin: { kind: HOLE, span, blank: true }, erased });
  ctx.holes.push({ id: made.id, span, is, from: ctx.st.explains.length, late: false });
  return { local: { ...local, scope: is ? solveHoles(ctx, made.scope, ref(made.id), is, span) : made.scope },
    result: { id: made.id, tainted: false, erased } };
}

function build(ctx: Ctx, local: Local, e: Expr, given: Given | null, snap: Snapshot, where: string): Out {
  switch (e.kind) {
    case "var": {
      const name = e.name.name;
      if (name === null) return fail(e.span, () =>
        "`_` stands only for a whole argument or inside a type (§16)");
      const found = lookup(local.scope, name);
      if (!found) return notValue(ctx, { name, span: e.name.span });
      occur(ctx, e.name.span, local, found.id);
      point(ctx, local.scope, e.span, ref(found.id));
      return produced(ctx, local, given, [{ id: found.id, tainted: local.tainted.has(name),
        erased: found.erased || local.erased.has(name) }], e.span, e);
    }
    case "app": {
      const name = e.head.name, g = global(ctx, name);
      if (g && g.kind !== "binding") occur(ctx, e.head.span, local, g);
      if (g?.kind === "fn") return call(ctx, local, e, name, g.sig, given);
      if (g?.kind === "type" || g?.kind === "ctor") return construct(ctx, local, e, g.sig, given);
      return fail(e.head.span, () => lookup(local.scope, name)
        ? `${code(name)} is a value, and only functions, type constructors and value constructors are applied (§4)`
        : `${code(name)} is not in scope`);
    }
    case "tuple": {
      if (given && given.wants.length !== e.elems.length)
        miscount(e.span, given.wants.length, `tuple has ${plural(e.elems.length, "element")}`);
      const results: Result[] = [], elems: Expr[] = [];
      e.elems.forEach((el, i) => {
        const w = given?.wants[i];
        const label = given?.label;
        const out = expr(ctx, local, el, given && w ? { wants: [w],
          env: [...given.env, ...results.map(r => ref(r.id))], whole: false,
          ...(label ? { label: () => label(i) } : {}) } : null, where);
        local = out.local;
        results.push(single(out, el.span));
        elems.push(out.tree);
      });
      return { local, results, tree: { ...e, elems } };
    }
    case "block": {
      const level: Ctx = { ...ctx, holes: [] }, stmts: Stmt[] = [], named: Named[] = [];
      let inner = local;
      for (const s of e.stmts) {
        const o = stmt(level, inner, s);
        inner = o.local;
        named.push(...o.bound);
        stmts.push(o.tree);
      }
      const fin = expr(ctx, inner, e.final, given, where);
      return {
        local: { ...local, scope: forget(fin.local.scope, local.scope, named), taintedBy: fin.local.taintedBy },
        results: fin.results,
        tree: { ...e, stmts, final: fin.tree },
      };
    }
    case "match": return match(ctx, local, e, given, snap);
    case "sorry": {
      const ann = annotation(ctx, local, e.tele, given);
      const o = opened(local, ann.tele, ann.env, "sorry", e.span, () => true);
      return produced(ctx, o.local, given, o.results, e.span, e);
    }
    case "removed": return fail(e.span, () => "internal: a removed expression was checked");
  }
}

function notValue(ctx: Ctx, { name, span }: Name): never {
  const g = global(ctx, name);
  return fail(span, () => !g ? `${code(name)} is not in scope`
    : `${code(name)} is ${describe(g)}, which is not a value: ` +
      (g.kind === "fn" ? "functions are not first class (§4)"
        : `it is applied, as in ${code(`${name}(${"sig" in g && !g.sig.params.length ? "" : "..."})`)}`));
}

function unmarked(e: App, why: string): void {
  const m = e.args.find(a => a.mark);
  if (m) fail(m.span, () => `only a call within its group has marks (§9), and ${why}`);
}

function opened(local: Local, tele: Telescope, env: readonly Term[], kind: string, span: Span,
    tainted: (i: number) => boolean): { local: Local; results: Result[] } {
  const o = open(local.scope, tele, env, (b, i) => ({ origin: { kind: `${kind}.${b.name ?? i + 1}`, span },
    tainted: tainted(i) }));
  return { local: { ...local, scope: o.scope }, results: o.entries.map((id, i) =>
    ({ id, tainted: tainted(i), erased: entry(o.scope, id).erased })) };
}

function args(ctx: Ctx, local: Local, name: string, params: Telescope, e: App, role: string,
    erasedArgs: boolean): { local: Local; results: Result[]; trees: Arg[]; mark: number } {
  if (e.args.length !== params.length)
    fail(e.span, () =>
      `${code(name)} takes ${plural(params.length, "argument")}, and ${are(e.args.length, "argument")} given`);
  const results: Result[] = [], trees: Arg[] = [], mark = ctx.holes.length;
  params.forEach((p, i) => {
    const a = e.args[i]!, env = results.map(r => ref(r.id));
    const label = () => labelled(role, p.name, i, name);
    const given: Given = { wants: [erasedArgs ? { ...p, mult: "erased" } : p], env, whole: false, label };
    if (erasedAt(given, 0)) erases(ctx, a.span);
    if (a.expr.kind === "var" && a.expr.name.name === null) {
      record(ctx, local, a.span, given);
      const type = subst(p.type, env), erased = ctx.erased || erasedAt(given, 0);
      if (!erased && !ctx.inType && !identical(local.scope, type, TYPE)) fail(a.span, () =>
        "`_` stands for an argument that is erased or has type `Type()`, or for part of a type (§16), " +
        `and ${label()} is none of these`);
      const h = hole(ctx, local, a.span, type, p.is && subst(p.is, env), erased);
      local = h.local;
      results.push(h.result);
      trees.push({ ...a, expr: { kind: "removed", span: a.expr.span } });
      return;
    }
    const out = expr(ctx, local, a.expr, given);
    local = out.local;
    results.push(single(out, a.span));
    trees.push({ ...a, expr: out.tree });
  });
  return { local, results, trees, mark };
}

function construct(ctx: Ctx, local: Local, e: App, sig: Signature, given: Given | null): Out {
  unmarked(e, `${code(sig.head.name)} is not a function`);
  const type = sig.head.kind === "type";
  const a = args(type ? { ...ctx, inType: true } : ctx, local, sig.head.name, sig.params, e,
    type ? "parameter" : "field", type && ctx.st.phase >= 2);
  const refs = trees(a.local.scope, a.results), tainted = a.results.some(r => r.tainted);
  const made = create(a.local.scope, subst(sig.ret, refs), app(sig.head, ...refs),
    { origin: { kind: APP, span: e.span }, tainted });
  point(ctx, made.scope, e.span, ref(made.id));
  return produced(ctx, { ...a.local, scope: made.scope }, given, [{ id: made.id, tainted, erased: false }], e.span,
    type ? { kind: "removed", span: e.span } : { ...e, args: a.trees });
}

function call(ctx: Ctx, local: Local, e: App, name: string, sig: FnSig | null, given: Given | null): Out {
  if (ctx.skeleton) return fail(e.span, () =>
    `${code(name)} is a function, and a type contains no function call (§3)`);
  if (!sig) return fail(e.span, () => `${code(name)}'s parameters and returns are still being checked here`);
  const fn = ctx.fn?.group.includes(name) ? ctx.fn : null;
  if (!fn) unmarked(e, ctx.fn ? `${code(name)} is not in ${code(ctx.fn.name)}'s group`
    : "top-level code calls any function unmarked");
  const plan = fn && marks(e, name, sig, fn);
  const a = args(ctx, local, name, sig.params, e, "parameter", false);
  if (fn && plan) decrease(a.local.scope, e, a.results, fn, plan);
  const tainted = sig.tainted || a.results.some(r => r.tainted);
  const o = opened(a.local, sig.returns, trees(a.local.scope, a.results), name, e.span, () => tainted);
  return close(ctx, produced(ctx, o.local, given, o.results, e.span, { ...e, args: a.trees }), a.mark, true);
}

interface Plan { subs: number[]; k: number }

function marks(e: App, name: string, sig: FnSig, fn: FnCtx): Plan {
  const subs = sig.subterm.flatMap((s, i) => (s ? [i] : []));
  const at = e.args.findIndex(a => a.mark === "subterm"), k = subs.indexOf(at);
  const within = `this call is within ${code(name)}'s group, so it must mark one argument \`subterm\``;
  if (k < 0) fail(e.args[at]?.span ?? e.span, () => !subs.length
    ? `${within}, and ${code(name)} has no \`subterm\` parameter to mark an argument for (§9)`
    : at < 0 ? `${within}: the argument for one of ${code(name)}'s \`subterm\` parameters (§9)`
    : `${labelled("parameter", sig.params[at]?.name ?? null, at, name)} is not a \`subterm\` parameter, ` +
      "so its argument is not marked `subterm` (§9)");
  e.args.forEach((a, i) => {
    const want = i === at ? "subterm" : subs.slice(0, k).includes(i) ? "same" : null;
    if (a.mark !== want) fail(a.span, () => want
      ? `this argument is for a \`subterm\` parameter of ${code(name)} before the one marked \`subterm\`, ` +
        "so it is marked `same` (§9)"
      : `this argument is not marked: only the arguments for ${code(name)}'s \`subterm\` parameters ` +
        "up to the one marked `subterm` are (§9)");
  });
  if (fn.subterms.length <= k)
    fail(e.span, () => `this marks ${code(name)}'s \`subterm\` parameter ${k + 1} \`subterm\`, ` +
      `and ${code(fn.name)} has only ${plural(fn.subterms.length, "`subterm` parameter")} (§9)`);
  return { subs, k };
}

function decrease(scope: Scope, e: App, results: readonly Result[], fn: FnCtx, { subs, k }: Plan): void {
  subs.slice(0, k + 1).forEach((p, j) => {
    const arg = ref(results[p]!.id), own = fn.subterms[j]!, strict = j === k;
    if (strict ? !isStrictSubterm(scope, arg, ref(own)) : !identical(scope, arg, ref(own)))
      fail(e.args[p]!.span, () =>
        `${show(scope, arg)} is not ${strict ? "a strict subterm of" : "canonically identical to"} ` +
        `${code(label(scope, own))}, ${code(fn.name)}'s \`subterm\` parameter ${j + 1}, ` +
        `which is ${show(scope, ref(own))} here (§9)`);
  });
}

function match(ctx: Ctx, local: Local, e: Match, given: Given | null, snap: Snapshot): Out {
  const erased = e.mult === "erased";
  const scrut = closed(erased ? { ...ctx, erased } : ctx, local, e.scrut, null, "the scrutinee of a `many` match");
  const s = single(scrut, e.scrut.span), inner = scrut.local;
  const ann = annotation(ctx, inner, e.ann, given);
  const fs = forcings(ctx, inner, s.id, e.scrut.span, e.branches.map(b => b.pat), e.span, erased);
  const refuted = snap.refutations = refutations(fs);
  const branchOf = (pat: Pattern): Forcing => fs.find(f => f.pat === pat)!;
  for (const br of e.branches) {
    survivor(branchOf(br.pat), br.pat.span, "the match has no branch for it");
    names(ctx, inner, br.pat.fields);
  }
  const missing = fs.filter(f => f.forced.ok && !f.pat).map(f => f.name);
  if (missing.length) fail(e.span, () =>
    `no branch for ${missing.map(code).join(", ")}, ` +
    `which ${missing.length === 1 ? "is" : "are"} not refuted here (§10)`);
  const live = erased ? e.branches.filter(br => !absurd(br.body)) : e.branches, second = live[1];
  if (erased) for (const span of [{ start: e.multStart, end: e.scrut.span.end },
    ...e.branches.map(br => live.includes(br) ? br.pat.span : br.span)]) erases(ctx, span);
  if (erased && second && ann.tele.some(b => b.mult === "many"))
    fail(second.span, () =>
      "an erased match with a `many` annotation entry has at most one branch that is not absurd, " +
      "a branch being absurd when its body is a match with no branches, possibly the final expression of a block, " +
      "since evaluation has no value to choose a branch by");
  const wants = ann.tele.map((b, i) => erasedAt(given, i) ? { ...b, mult: "erased" as const } : b);
  const label = Array.isArray(e.ann) ? (i: number) => labelled("annotation entry", ann.tele[i]?.name ?? null, i)
    : given?.label;
  const bodies = e.branches.map(br => {
    const won = survivor(branchOf(br.pat), br.pat.span, "");
    const bound = bind(ctx, { ...inner, scope: won.scope, taintedBy: reach(inner, s, e.scrut.span) }, br.pat.fields,
      won.fields).local;
    return closed(ctx, bound, br.body, { wants, env: ann.env, whole: true, ...(label ? { label } : {}) });
  });
  snap.refutations = [...refuted, ...e.branches.filter(br => !live.includes(br)).map(br =>
    ({ ctor: br.pat.ctor.name, kind: "absurd" as const, derivation: () => [] }))];
  const taint = (i: number) => s.tainted || bodies.some(b => b.results[i]?.tainted === true);
  const o = opened(inner, ann.tele, ann.env, "match", e.span, taint);
  return produced(ctx, o.local, given, o.results, e.span,
    { ...e, scrut: scrut.tree, branches: e.branches.flatMap((br, j) => live.includes(br)
      ? [{ ...br, body: bodies[j]!.tree }] : []) });
}

function annotation(ctx: Ctx, local: Local, tele: Tele, given: Given | null): { tele: Telescope; env: readonly Ref[] } {
  if (Array.isArray(tele)) return { tele: telescope(ctx, local, tele, "binder").tele, env: [] };
  if (!given?.whole) return fail(tele.span, () =>
    "`_` stands for the whole telescope given at its position, and none is given here (§10)");
  const wants = given.wants.map(w => w.type ? { ...w, type: w.type }
    : fail(tele.span, () => "internal: an undetermined entry in a whole telescope"));
  point(ctx, local.scope, tele.span, given);
  return { tele: wants, env: given.env };
}

function dataCtors(ctx: Ctx, scope: Scope, id: EntryId, span: Span): (Global & { kind: "ctor" })[] {
  const type = canon(scope, entry(scope, id).type);
  const g = type.tag === "app" ? global(ctx, type.head.name) : undefined;
  const ctors = g?.kind === "type" && g.done ? g.ctors : null;
  if (!ctors) return fail(span, () => g?.kind === "type" && !g.ctors
    ? "this has type `Type()`, and a value of type `Type()` cannot be the scrutinee of a `match` or pattern `let` (§4)"
    : g?.kind === "type" ? `${code(g.name)} is still being declared here`
    : `the scrutinee's type ${show(scope, type)} is not a data type (§10)`);
  return ctors.map(name => {
    const c = global(ctx, name);
    return c?.kind === "ctor" ? c : fail(span, () => `${code(name)} is not declared at this point`);
  });
}

function forcings(ctx: Ctx, local: Local, id: EntryId, scrutSpan: Span, pats: readonly Pattern[], at: Span,
    erased: boolean): Forcing[] {
  const ctors = dataCtors(ctx, local.scope, id, scrutSpan), seen = new Set<string>();
  for (const p of pats) {
    const name = p.ctor.name, c = ctors.find(x => x.name === name);
    if (!c) fail(p.ctor.span, () =>
      `${code(name)} is not a value constructor of the scrutinee's type ` +
      show(local.scope, entry(local.scope, id).type));
    if (seen.has(name)) fail(p.span, () => `${code(name)} already has a branch (§10)`);
    seen.add(name);
    if (p.fields.length !== c.sig.params.length) fail(p.span, () =>
      `${code(name)} has ${plural(c.sig.params.length, "field")}, and this pattern names ${p.fields.length}`);
    occur(ctx, p.ctor.span, local, c);
  }
  return ctors.map(({ name, sig }) => {
    const pat = pats.find(p => p.ctor.name === name);
    const forced = force(local.scope, id, sig, pat?.span ?? at, (b, i) =>
      ({ origin: { kind: `${name}.${b.name ?? i + 1}`, span: pat?.fields[i]?.span ?? at,
        blank: pat?.fields[i]?.name === null },
      ...(erased ? { erased } : {}) }), (b, i) => pat ? pat.fields[i]?.name ?? null : `@${b.name ?? i + 1}`);
    return { name, forced, pat };
  });
}

const refutations = (fs: readonly Forcing[]): RefutationInfo[] =>
  fs.flatMap(f => f.forced.ok ? [] : [{ ctor: f.name, kind: "refuted" as const, derivation: f.forced.derivation }]);

const absurd = (e: Expr): boolean => e.kind === "match" ? !e.branches.length : e.kind === "block" && absurd(e.final);

function survivor(f: Forcing, span: Span, consequence: string): { scope: Scope; fields: EntryId[] } {
  const forced = f.forced;
  if (!forced.ok)
    return fail(span, () => `${code(f.name)} is refuted here, so ${consequence} (§10)`, forced.derivation);
  return forced;
}

function names(ctx: Ctx, local: Local, ids: readonly Id[]): void {
  const seen = new Set<string>();
  for (const id of ids) newName(ctx, local, id, seen);
}

const never = (): boolean => false;

function bind(ctx: Ctx | null, local: Local, ids: readonly Id[], entries: readonly EntryId[],
    tainted: (i: number) => boolean = never, erased: (i: number) => boolean = never): { local: Local; bound: Named[] } {
  let scope = local.scope;
  const sets = { tainted: new Set(local.tainted), erased: new Set(local.erased) }, bound: Named[] = [];
  ids.forEach(({ name, span }, i) => {
    const id = entries[i];
    if (id === undefined) return;
    if (name === null) { scope = blank(scope, id, span); return; }
    scope = withName(scope, id, name);
    bound.push({ name, id });
    if (tainted(i)) sets.tainted.add(name);
    if (erased(i)) sets.erased.add(name);
  });
  const out = { ...local, scope, ...sets };
  if (ctx) ids.forEach(({ name, span }, i) => {
    const id = entries[i];
    if (name === null || id === undefined) return;
    occur(ctx, span, out, id);
    if (entry(scope, id).erased || sets.erased.has(name)) erases(ctx, span);
  });
  return { local: out, bound };
}

function erasedBinder(ctx: Ctx, b: LetBinder): void {
  if (b.mult === "erased") erases(ctx, { start: b.multStart, end: b.name.span.end });
}

const holed = (t: WrittenTerm): boolean => t.hole === true || (t.args ?? []).some(holed);

function letWants(ctx: Ctx, site: Local, binders: readonly LetBinder[]): { wants: Want[]; scope: Scope } {
  let local = site;
  const ids: EntryId[] = [], untyped = new Set<string>(), named: Named[] = [], first = ctx.holes.length;
  const unknown = (t: WrittenTerm): WrittenTerm | undefined => untyped.has(t.head.name) ? t
    : (t.args ?? []).map(unknown).find(u => u);
  for (const b of binders) {
    record(ctx, local, b.span, null);
    erasedBinder(ctx, b);
    const u = b.ann && unknown(b.ann.term);
    if (u) fail(u.span, () => `${code(u.head.name)} has no type here: give it one before referring to it`);
    const o = b.ann && opening(ctx, local, { ...b, ann: b.ann }, "binder", false, true);
    if (!o && b.name.name !== null) untyped.add(b.name.name);
    local = o?.local ?? local;
    named.push(...o?.bound ?? []);
    ids.push(o?.id ?? -1);
  }
  for (const h of ctx.holes.slice(first)) h.late = true;
  const wants = binders.map((b, i) => {
    const id = ids[i]!;
    return id >= 0 ? abstracted(local.scope, b, id, ids)
      : { name: b.name.name, type: null, is: null, mult: b.mult ?? "many", span: b.span };
  });
  return { wants, scope: ctx.holes.length > first ? forget(local.scope, site.scope, named) : site.scope };
}

export function stmt(ctx: Ctx, local: Local, s: Stmt, comptime?: Comptime): StmtOut {
  switch (s.kind) {
    case "inspect":
      record(ctx, local, s.span, null, true);
      return { local, tree: s, bound: [] };
    case "let": {
      record(ctx, local, s.span, null);
      if (s.binders.every(b => b.mult === "erased")) erases(ctx, s.span);
      names(ctx, local, s.binders.map(b => b.name));
      const c: Ctx = { ...ctx, holes: [] }, given = letWants(c, local, s.binders);
      const out = close(c, expr(c, { ...local, scope: given.scope }, s.rhs, { wants: given.wants, env: [],
        whole: s.binders.every(b => b.ann && !holed(b.ann.term)),
        label: i => labelled("binder", s.binders[i]?.name.name ?? null, i) }), 0);
      const b = bind(ctx, out.local, s.binders.map(x => x.name), out.results.map(r => r.id),
        i => out.results[i]!.tainted, i => s.binders[i]!.mult === "erased");
      return { local: b.local, tree: { ...s, rhs: out.tree }, bound: b.bound };
    }
    case "patlet": {
      const snap = record(ctx, local, s.span, null), erased = s.mult === "erased";
      if (s.comptime && erased) fail(s.span, () =>
        "a `comptime` pattern `let` evaluates its right-hand side (§11), so it cannot be erased (§16)");
      if (erased) erases(ctx, s.span);
      names(ctx, local, s.pat.fields);
      const out = closed(erased ? { ...ctx, erased } : ctx, local, s.rhs, null,
        "the right-hand side of a `many` pattern `let`"), r = single(out, s.rhs.span);
      const fs = forcings(ctx, out.local, r.id, s.rhs.span, [s.pat], s.span, erased);
      snap.refutations = refutations(fs);
      if (s.comptime) comptime?.(out.tree, r.tainted);
      const mine = fs.find(f => f.pat === s.pat)!;
      const won = survivor(mine, s.pat.span, "this pattern `let` cannot match");
      const other = s.comptime ? undefined : fs.find(f => f !== mine && f.forced.ok);
      if (other) fail(s.pat.span, () =>
        `${code(other.name)} is not refuted here, ` +
        "and exactly one value constructor must survive forcing at a pattern `let` (§10)");
      const b = bind(ctx, { ...out.local, scope: won.scope, taintedBy: reach(out.local, r, s.rhs.span) },
        s.pat.fields, won.fields);
      return { local: b.local, tree: { ...s, rhs: out.tree }, bound: b.bound };
    }
  }
}

const skeleton = (t: WrittenTerm): Expr => t.args === null
  ? { kind: "var", name: t.hole ? { name: null, span: t.span } : t.head, span: t.span }
  : { kind: "app", head: t.head, args: t.args.map(a => ({ mark: null, expr: skeleton(a), span: a.span })),
    span: t.span };

export function term(ctx: Ctx, local: Local, t: WrittenTerm, kind: Ann["kind"] = "is",
    open = false): Result & { local: Local } {
  const c = { ...ctx, skeleton: true, erased: ctx.erased || ctx.st.phase >= 2, holes: open ? ctx.holes : [] };
  if (t.hole && kind === "is") fail(t.span, () => "`_` stands only for a whole argument or inside a type (§16)");
  const h = t.hole ? hole(c, local, t.span, TYPE, null, c.erased) : null;
  const made = h ? { local: h.local, results: [h.result], tree: skeleton(t) } : expr(c, local, skeleton(t), null);
  const out = open ? made : close(c, made, 0);
  return { local: out.local, ...single(out, t.span) };
}

function isType(scope: Scope, id: EntryId, span: Span): void {
  if (!identical(scope, entry(scope, id).type, TYPE))
    fail(span, () =>
      `${show(scope, ref(id))} is not a type: its type is ${show(scope, entry(scope, id).type)}, not \`Type()\` (§3)`);
}

export function annotate(ctx: Ctx, local: Local, ann: Ann,
    open = false): { local: Local; type: Term; is: Term | null; tainted: boolean } {
  const t = term(ctx, local, ann.term, ann.kind, open), scope = t.local.scope, it = written(scope, ref(t.id));
  if (ann.kind === "is") return { local: t.local, type: written(scope, entry(scope, t.id).type), is: it,
    tainted: t.tainted };
  isType(scope, t.id, ann.term.span);
  return { local: t.local, type: it, is: null, tainted: t.tainted };
}

interface Checked { local: Local; ids: EntryId[]; tele: Telescope; tainted: boolean }

function opening(ctx: Ctx, local: Local, b: WrittenBinder, kind: string, occurs = true,
    open = false): { local: Local; id: EntryId; tainted: boolean; bound: Named[] } {
  const a = annotate(ctx, local, b.ann, open);
  const made = create(a.local.scope, a.type, a.is, { origin: { kind, span: b.span }, erased: b.mult === "erased" });
  const bound = bind(occurs ? ctx : null, { ...a.local, scope: made.scope }, [b.name], [made.id]);
  return { local: bound.local, id: made.id, tainted: a.tainted, bound: bound.bound };
}

function abstracted(scope: Scope, b: { name: Id; mult: Mult | null; span: Span }, id: EntryId,
    all: readonly EntryId[]): Binder {
  const e = entry(scope, id);
  return { name: b.name.name, type: abstract(scope, e.type, all), is: e.rule && abstract(scope, e.rule.term, all),
    mult: b.mult ?? "many", span: b.span };
}

export function telescope(ctx: Ctx, local: Local, binders: readonly WrittenBinder[], kind: string,
    outer: readonly EntryId[] = []): Checked {
  const seen = new Set<string>(), ids: EntryId[] = [];
  let tainted = false;
  for (const b of binders) {
    record(ctx, local, b.span, null);
    erasedBinder(ctx, b);
    newName(ctx, local, b.name, seen);
    const o = opening(ctx, local, b, kind);
    local = o.local;
    tainted ||= o.tainted;
    ids.push(o.id);
  }
  const all = [...outer, ...ids];
  return { local, ids, tainted, tele: binders.map((b, i) => abstracted(local.scope, b, ids[i]!, all)) };
}

export function header(ctx: Ctx, local: Local, h: Header): { params: Checked; returns: Checked } {
  const params = telescope(ctx, local, h.params, "param");
  return { params, returns: telescope(ctx, params.local, h.returns, "binder", params.ids) };
}
