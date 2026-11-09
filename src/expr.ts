import type { Ann, Arg, Expr, Id, Mult, Pattern, Span, Stmt, Tele, Term as Written } from "./syntax.ts";
import { TYPE, abstract, adopt, app, canon, create, entry, identical, isStrictSubterm, lookup, ref, subst, withName } from "./terms.ts";
import type { EntryId, Scope, Signature, Telescope, Term } from "./terms.ts";
import { force, open } from "./telescope.ts";
import type { Forced } from "./telescope.ts";
import { label, render } from "./render.ts";
import type { RefutationInfo } from "./api.ts";
import { APP, describe, fail, fresh, global, point, record, written } from "./context.ts";
import type { Ctx, FnCtx, FnSig, Given, Local, Result, Snapshot, Want } from "./context.ts";

type App = Expr & { kind: "app" };
type Match = Expr & { kind: "match" };
export interface Out { local: Local; results: Result[]; tree: Expr }
export interface Named { name: string; id: EntryId }
export interface StmtOut { local: Local; poison: boolean; tree: Stmt; bound: Named[] }
export type Comptime = (tree: Expr, tainted: boolean) => void;
interface Forcing { name: string; forced: Forced; pat: Pattern | undefined }
interface Binderish { name: Id; ann: Ann; mult: Mult | null; span: Span }

const show = (scope: Scope, t: Term): string => render(scope, t).text;
const trees = (scope: Scope, results: readonly Result[]): Term[] => results.map(r => written(scope, ref(r.id)));
export const plural = (n: number, what: string): string => `${n} ${what}${n === 1 ? "" : "s"}`;

export function single(out: Out, span: Span): Result {
  const [r] = out.results;
  if (!r || out.results.length > 1) fail(span, () => `this produces ${plural(out.results.length, "value")}, and one is expected here (§8)`);
  return r;
}

export function expr(ctx: Ctx, local: Local, e: Expr, given: Given | null): Out {
  const out = build(ctx, local, e, given, record(ctx, local, e.span, given));
  return out.results.every(r => r.tainted) ? { ...out, tree: { kind: "removed", span: e.span } } : out;
}

function produced(local: Local, given: Given | null, results: Result[], span: Span, tree: Expr): Out {
  if (given) against(local.scope, given, results.map(r => r.id), span);
  return { local, results, tree };
}

function against(scope: Scope, given: Given, ids: readonly EntryId[], span: Span): void {
  const n = given.wants.length;
  if (ids.length !== n) fail(span, () => `${plural(n, "value")} ${n === 1 ? "is" : "are"} expected here, and this produces ${ids.length}`);
  given.wants.forEach((w, i) => {
    const id = ids[i]!, env = [...given.env, ...ids.slice(0, i).map(ref)];
    const what = () => w.name !== null ? `\`${w.name}\`` : n === 1 ? "the value expected here" : `value ${i + 1}`;
    const type = w.type && subst(w.type, env), is = w.is && subst(w.is, env);
    if (type && !identical(scope, type, entry(scope, id).type))
      fail(span, () => `${what()} must have type ${show(scope, type)}, and this has type ${show(scope, entry(scope, id).type)}`);
    if (is && !identical(scope, is, ref(id)))
      fail(span, () => `${what()} must be ${show(scope, is)}, and this is ${show(scope, ref(id))}`);
  });
}

function build(ctx: Ctx, local: Local, e: Expr, given: Given | null, snap: Snapshot): Out {
  switch (e.kind) {
    case "var": {
      const name = e.name.name;
      if (name === null) return fail(e.span, () => "`_` as an argument (§16) is not supported by this checker yet");
      const found = lookup(local.scope, name);
      if (!found) return notValue(ctx, e.name);
      point(ctx, local.scope, e.span, ref(found.id));
      return produced(local, given, [{ id: found.id, tainted: local.tainted.has(name) }], e.span, e);
    }
    case "app": {
      const name = e.head.name ?? "_", g = global(ctx, name);
      if (g?.kind === "fn") return call(ctx, local, e, name, g.sig, given);
      if (g?.kind === "type" || g?.kind === "ctor") return construct(ctx, local, e, g.sig, given);
      return fail(e.head.span, () => lookup(local.scope, name)
        ? `${name} is a value, and only functions, type constructors and value constructors are applied (§4)`
        : `${name} is not in scope`);
    }
    case "tuple": {
      if (given && given.wants.length !== e.elems.length)
        fail(e.span, () => `${plural(given.wants.length, "value")} expected here, and this tuple has ${plural(e.elems.length, "element")}`);
      const results: Result[] = [], elems: Expr[] = [];
      e.elems.forEach((el, i) => {
        const w = given?.wants[i];
        const out = expr(ctx, local, el, given && w ? { wants: [w], env: [...given.env, ...results.map(r => ref(r.id))], whole: false } : null);
        local = out.local;
        results.push(single(out, el.span));
        elems.push(out.tree);
      });
      return { local, results, tree: { ...e, elems } };
    }
    case "block": {
      const since = local.scope.supply.next;
      let inner = local, poisoned = false;
      const stmts: Stmt[] = [];
      for (const s of e.stmts) {
        const o = stmt(ctx, inner, s, false);
        inner = o.local;
        poisoned ||= o.poison;
        stmts.push(o.tree);
      }
      const fin = expr(ctx, inner, e.final, given);
      return {
        local: { scope: adopt(local.scope, fin.local.scope, since), tainted: local.tainted },
        results: fin.results.map(r => ({ ...r, tainted: r.tainted || poisoned })),
        tree: { ...e, stmts, final: fin.tree },
      };
    }
    case "match": return match(ctx, local, e, given, snap);
    case "sorry": {
      const ann = annotation(ctx, local, e.tele, given, e.span);
      const opened = open(local.scope, ann.tele, ann.env, (b, i) => ({ origin: { kind: `sorry.${b.name ?? i + 1}`, span: e.span }, tainted: true }));
      return produced({ ...local, scope: opened.scope }, given, opened.entries.map(id => ({ id, tainted: true })), e.span, e);
    }
    case "removed": return fail(e.span, () => "internal: a removed expression was checked");
  }
}

function notValue(ctx: Ctx, id: Id): never {
  const name = id.name ?? "_", g = global(ctx, name);
  return fail(id.span, () => !g ? `${name} is not in scope`
    : `${name} is ${describe(g)}, which is not a value: ${g.kind === "fn" ? "functions are not first class (§4)" : `it is applied, as in ${name}(...)`}`);
}

function unmarked(e: App, why: string): void {
  const m = e.args.find(a => a.mark);
  if (m) fail(m.span, () => `only a call within its group has marks (§9), and ${why}`);
}

function args(ctx: Ctx, local: Local, name: string, params: Telescope, e: App): { local: Local; results: Result[]; trees: Arg[] } {
  if (e.args.length !== params.length)
    fail(e.span, () => `${name} takes ${plural(params.length, "argument")}, and ${e.args.length} ${e.args.length === 1 ? "is" : "are"} given`);
  const results: Result[] = [], trees: Arg[] = [];
  params.forEach((p, i) => {
    const a = e.args[i]!;
    const out = expr(ctx, local, a.expr, { wants: [p], env: results.map(r => ref(r.id)), whole: false });
    local = out.local;
    results.push(single(out, a.span));
    trees.push({ ...a, expr: out.tree });
  });
  return { local, results, trees };
}

function construct(ctx: Ctx, local: Local, e: App, sig: Signature, given: Given | null): Out {
  unmarked(e, `${sig.head.name} is not a function`);
  const a = args(ctx, local, sig.head.name, sig.params, e);
  const refs = trees(a.local.scope, a.results), tainted = a.results.some(r => r.tainted);
  const made = create(a.local.scope, subst(sig.ret, refs), app(sig.head, ...refs), { origin: { kind: APP, span: e.span }, tainted });
  point(ctx, made.scope, e.span, ref(made.id));
  return produced({ ...a.local, scope: made.scope }, given, [{ id: made.id, tainted }], e.span, { ...e, args: a.trees });
}

function call(ctx: Ctx, local: Local, e: App, name: string, sig: FnSig | null, given: Given | null): Out {
  if (ctx.skeleton) return fail(e.span, () => `${name} is a function, and a type contains no function call (§3)`);
  if (!sig) return fail(e.span, () => `${name}'s parameters and returns are still being checked here`);
  const fn = ctx.fn?.group.includes(name) ? ctx.fn : null;
  if (!fn) unmarked(e, ctx.fn ? `${name} is not in ${ctx.fn.name}'s group` : "top-level code calls any function unmarked");
  const plan = fn && marks(e, name, sig, fn);
  const a = args(ctx, local, name, sig.params, e);
  if (fn && plan) decrease(a.local.scope, e, a.results, fn, plan);
  const tainted = sig.tainted || a.results.some(r => r.tainted);
  const opened = open(a.local.scope, sig.returns, trees(a.local.scope, a.results), (b, i) => ({ origin: { kind: `${name}.${b.name ?? i + 1}`, span: e.span }, tainted }));
  return produced({ ...a.local, scope: opened.scope }, given, opened.entries.map(id => ({ id, tainted })), e.span, { ...e, args: a.trees });
}

interface Plan { subs: number[]; k: number }

function marks(e: App, name: string, sig: FnSig, fn: FnCtx): Plan {
  const subs = sig.subterm.flatMap((s, i) => (s ? [i] : []));
  const at = e.args.findIndex(a => a.mark === "subterm"), k = subs.indexOf(at);
  if (k < 0) fail(e.args[at]?.span ?? e.span, () => at < 0
    ? `a call within its group marks one of ${name}'s \`subterm\` parameters \`subterm\` (§9)`
    : `parameter ${at + 1} of ${name} is not a \`subterm\` parameter, so its argument is not marked \`subterm\` (§9)`);
  e.args.forEach((a, i) => {
    const want = i === at ? "subterm" : subs.slice(0, k).includes(i) ? "same" : null;
    if (a.mark !== want) fail(a.span, () => want
      ? `this argument is for a \`subterm\` parameter of ${name} before the one marked \`subterm\`, so it is marked \`same\` (§9)`
      : `this argument is not marked: only the arguments for ${name}'s \`subterm\` parameters up to the one marked \`subterm\` are (§9)`);
  });
  if (fn.subterms.length <= k)
    fail(e.span, () => `this marks ${name}'s \`subterm\` parameter ${k + 1} \`subterm\`, and ${fn.name} has only ${plural(fn.subterms.length, "`subterm` parameter")} (§9)`);
  return { subs, k };
}

function decrease(scope: Scope, e: App, results: readonly Result[], fn: FnCtx, { subs, k }: Plan): void {
  subs.slice(0, k + 1).forEach((p, j) => {
    const arg = ref(results[p]!.id), own = fn.subterms[j]!, strict = j === k;
    if (strict ? !isStrictSubterm(scope, arg, ref(own)) : !identical(scope, arg, ref(own)))
      fail(e.args[p]!.span, () => `${show(scope, arg)} is not ${strict ? "a strict subterm of" : "canonically identical to"} ${label(scope, own)}, ` +
        `${fn.name}'s \`subterm\` parameter ${j + 1}, which is ${show(scope, ref(own))} here (§9)`);
  });
}

function match(ctx: Ctx, local: Local, e: Match, given: Given | null, snap: Snapshot): Out {
  const scrut = expr(ctx, local, e.scrut, null);
  const s = single(scrut, e.scrut.span), inner = scrut.local;
  const ann = annotation(ctx, inner, e.ann, given, e.span);
  const fs = forcings(ctx, inner, s.id, e.scrut.span, e.branches.map(b => b.pat), e.span);
  snap.refutations = refutations(fs);
  const branchOf = (pat: Pattern): Forcing => fs.find(f => f.pat === pat)!;
  for (const br of e.branches) {
    survivor(branchOf(br.pat), br.pat.span, "the match has no branch for it");
    names(ctx, inner, br.pat.fields);
  }
  const missing = fs.filter(f => f.forced.ok && !f.pat).map(f => f.name);
  if (missing.length) fail(e.span, () => `no branch for ${missing.join(", ")}, which ${missing.length === 1 ? "is" : "are"} not refuted here (§10)`);
  const bodies = e.branches.map(br => {
    const won = survivor(branchOf(br.pat), br.pat.span, "");
    return expr(ctx, bind({ ...inner, scope: won.scope }, br.pat.fields, won.fields).local, br.body, { wants: ann.tele, env: ann.env, whole: true });
  });
  const taint = (i: number) => s.tainted || bodies.some(b => b.results[i]?.tainted === true);
  const opened = open(inner.scope, ann.tele, ann.env, (b, i) => ({ origin: { kind: `match.${b.name ?? i + 1}`, span: e.span }, tainted: taint(i) }));
  return produced({ ...inner, scope: opened.scope }, given, opened.entries.map((id, i) => ({ id, tainted: taint(i) })), e.span,
    { ...e, scrut: scrut.tree, branches: e.branches.map((br, j) => ({ ...br, body: bodies[j]!.tree })) });
}

function annotation(ctx: Ctx, local: Local, tele: Tele, given: Given | null, span: Span): { tele: Telescope; env: readonly Term[] } {
  if (tele !== "_") return { tele: telescope(ctx, local, tele, "binder").tele, env: [] };
  if (!given?.whole) return fail(span, () => "`_` stands for the whole telescope given at its position, and none is given here (§10)");
  return { tele: given.wants.map(w => w.type ? { ...w, type: w.type } : fail(span, () => "internal: an undetermined entry in a whole telescope")), env: given.env };
}

function dataCtors(ctx: Ctx, scope: Scope, id: EntryId, span: Span): { name: string; sig: Signature }[] {
  const type = canon(scope, entry(scope, id).type);
  const g = type.tag === "app" ? global(ctx, type.head.name) : undefined;
  const ctors = g?.kind === "type" && g.done ? g.ctors : null;
  if (!ctors) return fail(span, () => g?.kind === "type" && !g.ctors
    ? "this has type Type(), and a value of type Type() cannot be the scrutinee of a `match` or pattern `let` (§4)"
    : g?.kind === "type" ? `${g.name} is still being declared here`
    : `the scrutinee's type ${show(scope, type)} is not a data type (§10)`);
  return ctors.map(name => {
    const c = global(ctx, name);
    return c?.kind === "ctor" ? { name, sig: c.sig } : fail(span, () => `${name} is not declared at this point`);
  });
}

function forcings(ctx: Ctx, local: Local, id: EntryId, scrutSpan: Span, pats: readonly Pattern[], at: Span): Forcing[] {
  const ctors = dataCtors(ctx, local.scope, id, scrutSpan), seen = new Set<string>();
  for (const p of pats) {
    const name = p.ctor.name ?? "_", c = ctors.find(x => x.name === name);
    if (!c) fail(p.ctor.span, () => `${name} is not a value constructor of the scrutinee's type ${show(local.scope, entry(local.scope, id).type)}`);
    if (seen.has(name)) fail(p.span, () => `${name} already has a branch (§10)`);
    seen.add(name);
    if (p.fields.length !== c.sig.params.length) fail(p.span, () => `${name} has ${plural(c.sig.params.length, "field")}, and this pattern names ${p.fields.length}`);
  }
  return ctors.map(({ name, sig }) => {
    const pat = pats.find(p => p.ctor.name === name);
    const forced = force(local.scope, id, sig, pat?.span ?? at, (b, i) => ({ origin: { kind: `${name}.${b.name ?? i + 1}`, span: pat?.fields[i]?.span ?? at } }));
    return { name, forced, pat };
  });
}

const refutations = (fs: readonly Forcing[]): RefutationInfo[] =>
  fs.flatMap(f => f.forced.ok ? [] : [{ ctor: f.name, derivation: f.forced.derivation }]);

function survivor(f: Forcing, span: Span, consequence: string): { scope: Scope; fields: EntryId[] } {
  const forced = f.forced;
  if (!forced.ok) return fail(span, () => `${f.name} is refuted here, so ${consequence} (§10): ${forced.derivation().map(l => l.text).join("; ")}`);
  return forced;
}

function names(ctx: Ctx, local: Local, ids: readonly Id[]): void {
  const seen = new Set<string>();
  for (const id of ids) fresh(ctx, local, id, seen);
}

function bind(local: Local, ids: readonly Id[], entries: readonly EntryId[], tainted: (i: number) => boolean = () => false): { local: Local; bound: Named[] } {
  let scope = local.scope;
  const set = new Set(local.tainted), bound: Named[] = [];
  ids.forEach(({ name }, i) => {
    const id = entries[i];
    if (name === null || id === undefined) return;
    scope = withName(scope, id, name);
    bound.push({ name, id });
    if (tainted(i)) set.add(name);
  });
  return { local: { scope, tainted: set }, bound };
}

export function stmt(ctx: Ctx, local: Local, s: Stmt, poison: boolean, comptime?: Comptime): StmtOut {
  switch (s.kind) {
    case "inspect":
      record(ctx, local, s.span, "none", true);
      return { local, poison: false, tree: s, bound: [] };
    case "let": {
      record(ctx, local, s.span, "none");
      names(ctx, local, s.binders.map(b => b.name));
      const wants: Want[] = s.binders.map(b => {
        const base = { name: b.name.name, mult: b.mult ?? "many", span: b.span };
        if (!b.ann) return { ...base, type: null, is: null };
        const a = annotate(ctx, local, b.ann);
        local = a.local;
        return { ...base, type: a.type, is: a.is };
      });
      const out = expr(ctx, local, s.rhs, { wants, env: [], whole: s.binders.every(b => b.ann) });
      const b = bind(out.local, s.binders.map(x => x.name), out.results.map(r => r.id), i => out.results[i]!.tainted || poison);
      return { local: b.local, poison: false, tree: { ...s, rhs: out.tree }, bound: b.bound };
    }
    case "patlet": {
      const snap = record(ctx, local, s.span, "none");
      names(ctx, local, s.pat.fields);
      const out = expr(ctx, local, s.rhs, null), r = single(out, s.rhs.span), tainted = r.tainted || poison;
      const fs = forcings(ctx, out.local, r.id, s.rhs.span, [s.pat], s.span);
      snap.refutations = refutations(fs);
      if (s.comptime) comptime?.(out.tree, tainted);
      const mine = fs.find(f => f.pat === s.pat)!;
      const won = survivor(mine, s.pat.span, "this pattern `let` cannot match");
      const other = s.comptime ? undefined : fs.find(f => f !== mine && f.forced.ok);
      if (other) fail(s.pat.span, () => `${other.name} is not refuted here, and exactly one value constructor must survive forcing at a pattern \`let\` (§10)`);
      const b = bind({ ...out.local, scope: won.scope }, s.pat.fields, won.fields);
      return { local: b.local, poison: tainted, tree: { ...s, rhs: out.tree }, bound: b.bound };
    }
  }
}

const skeleton = (t: Written): Expr => t.args === null
  ? { kind: "var", name: t.head, span: t.span }
  : { kind: "app", head: t.head, args: t.args.map(a => ({ mark: null, expr: skeleton(a), span: a.span })), span: t.span };

export function term(ctx: Ctx, local: Local, t: Written): Result & { local: Local } {
  const out = expr({ ...ctx, skeleton: true }, local, skeleton(t), null);
  return { local: out.local, ...single(out, t.span) };
}

export function isType(scope: Scope, id: EntryId, span: Span): void {
  if (!identical(scope, entry(scope, id).type, TYPE))
    fail(span, () => `${show(scope, ref(id))} is not a type: its type is ${show(scope, entry(scope, id).type)}, not Type() (§3)`);
}

export function annotate(ctx: Ctx, local: Local, ann: Ann): { local: Local; type: Term; is: Term | null; tainted: boolean } {
  const t = term(ctx, local, ann.term), scope = t.local.scope, it = written(scope, ref(t.id));
  if (ann.kind === "is") return { local: t.local, type: written(scope, entry(scope, t.id).type), is: it, tainted: t.tainted };
  isType(scope, t.id, ann.term.span);
  return { local: t.local, type: it, is: null, tainted: t.tainted };
}

export function telescope(ctx: Ctx, local: Local, binders: readonly Binderish[], kind: string, outer: readonly EntryId[] = []): { local: Local; ids: EntryId[]; tele: Telescope } {
  const seen = new Set<string>(), ids: EntryId[] = [];
  for (const b of binders) {
    record(ctx, local, b.span, "none");
    fresh(ctx, local, b.name, seen);
    const a = annotate(ctx, local, b.ann);
    const made = create(a.local.scope, a.type, a.is, { origin: { kind, span: b.span }, erased: b.mult === "erased" });
    local = bind({ ...a.local, scope: made.scope }, [b.name], [made.id]).local;
    ids.push(made.id);
  }
  const all = [...outer, ...ids], scope = local.scope;
  return {
    local, ids,
    tele: binders.map((b, i) => {
      const e = entry(scope, ids[i]!);
      return { name: b.name.name, type: abstract(scope, e.type, all), is: e.rule && abstract(scope, e.rule.term, all), mult: b.mult ?? "many", span: b.span };
    }),
  };
}
