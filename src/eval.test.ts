import { test } from "node:test";
import assert from "node:assert/strict";
import type { Binder, Expr, Fn, Id, Param, Pattern, Stmt, Term } from "./syntax.ts";
import { bindPattern, evalExpr, evalOne, evalStmt, InternalError, removed, showValue, type Env, type Fns } from "./eval.ts";

const span = { start: 0, end: 0 };
const id = (name: string): Id => ({ name: name === "_" ? null : name, span });
const term = (name: string): Term => ({ head: id(name), args: [], span });
const binder = (name: string): Binder => ({ name: id(name), ann: { kind: "type", term: term("Nat") }, mult: null, span });
const param = (name: string): Param => ({ ...binder(name), subterm: true });
const v = (name: string): Expr => ({ kind: "var", name: id(name), span });
const app = (head: string, ...args: Expr[]): Expr => ({ kind: "app", head: id(head), args: args.map(expr => ({ mark: null, expr, span })), span });
const tuple = (...elems: Expr[]): Expr => ({ kind: "tuple", elems, span });
const block = (stmts: Stmt[], final: Expr): Expr & { kind: "block" } => ({ kind: "block", stmts, final, span });
const pat = (ctor: string, ...fields: string[]): Pattern => ({ ctor: id(ctor), fields: fields.map(id), span });
const match = (scrut: Expr, n: number, ...branches: [Pattern, Expr][]): Expr =>
  ({ kind: "match", mult: null, scrut, ann: Array.from({ length: n }, (_, i) => binder(`r${i}`)), branches: branches.map(([p, body]) => ({ pat: p, body, span })), span });
const letT = (names: string[], rhs: Expr): Stmt => ({ kind: "let", binders: names.map(n => ({ name: id(n), ann: null, mult: null, span })), rhs, span });
const patlet = (p: Pattern, rhs: Expr): Stmt => ({ kind: "patlet", comptime: false, mult: null, pat: p, rhs, span });
const rem: Expr = { kind: "removed", span };
const fn = (name: string, params: string[], returns: number, body: Expr & { kind: "block" }): Fn =>
  ({ kind: "fn", name: id(name), params: params.map(param), returns: Array.from({ length: returns }, (_, i) => binder(`r${i}`)), body, span });

const nat = (n: number): Expr => n === 0 ? app("Zero") : app("Succ", nat(n - 1));
const natText = (n: number): string => n === 0 ? "Zero()" : `Succ(${natText(n - 1)})`;
const empty: Env = new Map();

const plus = fn("plus", ["m", "n"], 1, block([], match(v("m"), 1,
  [pat("Zero"), v("n")],
  [pat("Succ", "m1"), app("Succ", app("plus", v("m1"), v("n")))])));

const ack = fn("ack", ["m", "n"], 1, block([], match(v("m"), 1,
  [pat("Zero"), app("Succ", v("n"))],
  [pat("Succ", "m1"), match(v("n"), 1,
    [pat("Zero"), app("ack", v("m1"), app("Succ", app("Zero")))],
    [pat("Succ", "n1"), app("ack", v("m1"), app("ack", v("m"), v("n1")))])])));

const vuncons = fn("vuncons", ["A", "n", "v"], 2, block([patlet(pat("VCons", "_", "_", "h", "t"), v("v"))], tuple(v("h"), v("t"))));

const fns: Fns = new Map([plus, ack, vuncons].map(f => [f.name.name!, { fn: f, globals: empty }]));
const run = (e: Expr, env: Env = empty): string[] => evalExpr(fns, env, e).map(showValue);

test("plus adds Nats", () => {
  assert.deepEqual(run(app("plus", nat(2), nat(3))), [natText(5)]);
  assert.deepEqual(run(app("plus", nat(0), nat(0))), [natText(0)]);
});

test("ack on small inputs", () => {
  const expected = [[0, 0, 1], [1, 2, 4], [2, 2, 7], [2, 3, 9], [3, 3, 61]];
  for (const [m, n, r] of expected) assert.deepEqual(run(app("ack", nat(m!), nat(n!))), [natText(r!)]);
});

test("vuncons returns two values bound by a tuple let", () => {
  const vec = app("VCons", app("Nat"), nat(0), nat(1), app("VNil", app("Nat")));
  const e = block([letT(["h", "t"], app("vuncons", app("Nat"), nat(0), vec))], tuple(v("t"), v("h")));
  assert.deepEqual(run(e), ["VNil(Nat())", natText(1)]);
});

test("a block with lets, a wildcard binder and inspect", () => {
  const e = block([letT(["x"], nat(1)), { kind: "inspect", span }, letT(["_", "y"], tuple(v("x"), app("plus", v("x"), v("x"))))], v("y"));
  assert.deepEqual(run(e), [natText(2)]);
});

test("a pattern let binds fields", () => {
  const env = evalStmt(fns, empty, patlet(pat("Succ", "p"), nat(3)));
  assert.equal(showValue(env.get("p")!), natText(2));
  assert.throws(() => evalStmt(fns, empty, patlet(pat("Succ", "p"), nat(0))), InternalError);
});

test("comptime helpers: evaluate once, then bind", () => {
  const val = evalOne(fns, empty, app("Some", app("Nat"), nat(1)));
  assert.equal(val.head, "Some");
  assert.equal(showValue(bindPattern(empty, pat("Some", "_", "x"), val).get("x")!), natText(1));
});

test("showValue", () => {
  assert.equal(showValue({ head: "Type", args: [] }), "Type()");
  assert.equal(run(app("Vec", app("Type"), nat(1)))[0], `Vec(Type(), ${natText(1)})`);
  assert.equal(showValue({ head: "Some", args: [{ head: "Nat", args: [] }, removed] }), "Some(Nat(), _)");
});

test("a removed value flows through lets unobserved but throws when matched on", () => {
  assert.deepEqual(run(block([letT(["a", "b"], rem), letT(["c"], app("Succ", v("a")))], tuple(v("c"), nat(0)))), ["Succ(_)", natText(0)]);
  const two = fn("two", [], 2, block([], rem));
  const withTwo: Fns = new Map([...fns, ["two", { fn: two, globals: empty }]]);
  assert.deepEqual(evalExpr(withTwo, empty, block([letT(["a", "b"], app("two"))], tuple(v("b"), v("a")))).map(showValue), ["_", "_"]);
  assert.throws(() => run(match(rem, 1, [pat("Zero"), nat(0)])), InternalError);
  assert.throws(() => evalStmt(fns, empty, patlet(pat("Succ", "p"), rem)), InternalError);
  assert.throws(() => run({ kind: "sorry", tele: "_", span }), InternalError);
});

test("an erased match or pattern let binds its fields to the removed value and needs exactly one branch", () => {
  const erased = (m: Expr): Expr => ({ ...m, mult: "erased" } as Expr);
  assert.deepEqual(run(erased(match(rem, 1, [pat("Succ", "p"), app("Succ", v("p"))]))), ["Succ(_)"]);
  assert.throws(() => run(erased(match(rem, 1, [pat("Zero"), nat(0)], [pat("Succ", "p"), nat(1)]))), InternalError);
  assert.throws(() => run(erased(match(rem, 1))), InternalError);
  const env = evalStmt(fns, empty, { ...patlet(pat("Succ", "p"), rem), mult: "erased" } as Stmt);
  assert.equal(showValue(env.get("p")!), "_");
});
