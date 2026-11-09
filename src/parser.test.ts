import { test } from "node:test";
import assert from "node:assert/strict";
import { lex } from "./lexer.ts";
import { parse } from "./parser.ts";
import { readFileSync } from "node:fs";
import type { Phase, Program } from "./syntax.ts";
import { file, files } from "../tests/helpers.ts";

const pledgeFiles = files();
const nat = "data Nat() : Type() { Zero() : Nat(); Succ(pred : Nat()) : Nat(); }\n";

const ok = (source: string, phase: Phase = 1): Program => {
  const result = parse(source, phase);
  if (result.error) assert.fail(`${result.error.message()} at ${JSON.stringify(result.error.span)}`);
  return result.program;
};
const err = (source: string, phase: Phase = 1): { start: number; message: string } => {
  const { error } = parse(source, phase);
  if (!error) return assert.fail("expected a parse error");
  return { start: error.span.start, message: error.message() };
};

const strip = (value: unknown): unknown =>
  Array.isArray(value) ? value.map(strip)
  : value !== null && typeof value === "object"
    ? Object.fromEntries(Object.entries(value).filter(([k]) => k !== "span").map(([k, v]) => [k, strip(v)]))
    : value;
const id = (name: string | null) => ({ name });
const term = (head: string, args: unknown[] | null = []) => ({ head: id(head), args });
const variable = (name: string | null) => ({ kind: "var", name: id(name) });
const app = (head: string, ...args: unknown[]) => ({ kind: "app", head: id(head), args: args.map(expr => ({ mark: null, expr })) });

test("every tests/*.pledge parses in its phase and every later one", () => {
  assert.ok(pledgeFiles.length >= 10);
  for (const f of pledgeFiles) for (const phase of f.startsWith("phase2_") ? [2] as const : [1, 2] as const) {
    const { error } = parse(file(f), phase);
    assert.ok(!error, `${f} (phase ${phase}): ${error?.message() ?? ""}`);
  }
});

test("DESIGN.md's code appears verbatim in tests/*.pledge", () => {
  const design = readFileSync(new URL("../DESIGN.md", import.meta.url), "utf8");
  const examples = pledgeFiles.map(file);
  const blocks = [...design.matchAll(/```\n([\s\S]*?)```/g)].map(m => m[1]!).filter(block => !parse(block, 1).error);
  assert.equal(blocks.length, 7);
  const inline = [
    "let y is Succ(n) = e;",
    "let x = VCons(Nat(), Zero(), Zero(), VNil(Nat()));",
    "let (h, t) = vuncons(A, n, v);",
    "VCons(Nat(), Zero(), x, VNil(Nat()))",
    "fn decideEven(n : Nat()) -> (r : Option(Even(n)))",
    "sorry(x is Zero())",
  ];
  for (const code of [...blocks, ...inline]) assert.ok(examples.some(example => example.includes(code)), code);
});

test("vhead's shape", () => {
  const program = ok(file("design_vhead.pledge"));
  assert.deepEqual(program.tops.map(t => t.kind), ["data", "data", "fn"]);
  assert.deepEqual(strip(program.tops[2]), {
    kind: "fn",
    name: id("vhead"),
    params: [
      { name: id("A"), ann: { kind: "type", term: term("Type") }, mult: null, subterm: false },
      { name: id("n"), ann: { kind: "type", term: term("Nat") }, mult: null, subterm: false },
      { name: id("v"), ann: { kind: "type", term: term("Vec", [term("A", null), term("Succ", [term("n", null)])]) }, mult: null, subterm: false },
    ],
    returns: [{ name: id("x"), ann: { kind: "type", term: term("A", null) }, mult: null }],
    body: {
      kind: "block",
      stmts: [{ kind: "patlet", comptime: false, mult: null, pat: { ctor: id("VCons"), fields: [id(null), id(null), id("hd"), id(null)] }, rhs: variable("v") }],
      final: variable("hd"),
    },
  });
});

test("ack's marks and nested match", () => {
  const program = ok(file("design_ack.pledge"));
  const fn = program.tops[1];
  assert.ok(fn?.kind === "fn");
  assert.deepEqual(fn.params.map(p => p.subterm), [true, true]);
  const outer = fn.body.final;
  assert.ok(outer.kind === "match");
  assert.deepEqual(outer.branches.map(b => b.pat.ctor.name), ["Zero", "Succ"]);
  const inner = outer.branches[1]?.body;
  assert.ok(inner?.kind === "match");
  assert.deepEqual(strip(inner.branches[1]?.body), {
    kind: "app",
    head: id("ack"),
    args: [
      { mark: "subterm", expr: variable("m1") },
      { mark: null, expr: { kind: "app", head: id("ack"), args: [{ mark: "same", expr: variable("m") }, { mark: "subterm", expr: variable("n1") }] } },
    ],
  });
});

test("mutual data, empty match, comptime, sorry and statements", () => {
  const evenOdd = ok(file("design_even_odd.pledge")).tops[1];
  assert.ok(evenOdd?.kind === "mutual");
  assert.deepEqual(evenOdd.decls.map(d => d.name.name), ["Even", "Odd"]);
  const iszero = ok(file("design_iszero.pledge")).tops[2];
  assert.ok(iszero?.kind === "fn" && iszero.body.final.kind === "match");
  assert.deepEqual(strip(iszero.body.final.branches[1]?.body), { kind: "match", mult: null, scrut: variable("p"), ann: [{ name: id("r"), ann: { kind: "type", term: term("Nat") }, mult: null }], branches: [] });
  const reflection = ok(file("design_reflection.pledge")).tops.at(-1);
  assert.deepEqual(strip(reflection), {
    kind: "patlet", comptime: true, mult: null,
    pat: { ctor: id("Some"), fields: [id(null), id("p")] },
    rhs: app("decideEven", app("Succ", app("Succ", app("Zero")))),
  });
  assert.deepEqual(strip(ok(`${nat}let y = sorry(x is Zero());`).tops[1]), {
    kind: "let", binders: [{ name: id("y"), ann: null, mult: null }], rhs: { kind: "sorry", tele: [{ name: id("x"), ann: { kind: "is", term: term("Zero") }, mult: null }] },
  });
  assert.deepEqual(strip(ok(`${nat}goal Nat(); qed sorry(_); inspect; print (Zero(), x);`).tops.slice(1)), [
    { kind: "goal", type: term("Nat") },
    { kind: "qed", expr: { kind: "sorry", tele: "_" } },
    { kind: "inspect" },
    { kind: "print", expr: { kind: "tuple", elems: [app("Zero"), variable("x")] } },
  ]);
  assert.deepEqual(strip(ok("let (a, _ : Nat(), c is Zero()) = { inspect; match x : _ { Zero() => (y); } };").tops[0]), {
    kind: "let",
    binders: [{ name: id("a"), ann: null, mult: null }, { name: id(null), ann: { kind: "type", term: term("Nat") }, mult: null }, { name: id("c"), ann: { kind: "is", term: term("Zero") }, mult: null }],
    rhs: { kind: "block", stmts: [{ kind: "inspect" }], final: { kind: "match", mult: null, scrut: variable("x"), ann: "_", branches: [{ pat: { ctor: id("Zero"), fields: [] }, body: { kind: "tuple", elems: [variable("y")] } }] } },
  });
});

test("a non-ASCII character's error spans that character alone", () => {
  const span = (source: string) => lex(source, 1).at(-1)!.span;
  assert.deepEqual(span("let x = Zer\u00f6();"), { start: 11, end: 12 });
  assert.deepEqual(span("let x = \u{1d4b3};"), { start: 8, end: 10 });
});

test("spans are offsets into the source string", () => {
  const program = ok("  let x = Zero(); -- c\nprint x;");
  assert.deepEqual(program.tops.map(t => t.span), [{ start: 2, end: 17 }, { start: 23, end: 31 }]);
  assert.deepEqual(program.span, { start: 0, end: 31 });
});

test("extra semicolons", () => {
  ok(`${nat};;fn f(n : Nat()) -> (r : Nat()) { let x = n;; { x }; };; let y = Zero();;;`);
  ok("mutual { data A() : Type() {}; data B() : Type() { C() : B();; }; };");
  assert.equal(err(";").start, 0);
  assert.match(err("let x = { y; };").message, /expected `}`/);
});

test("errors", () => {
  const cases: [string, number, RegExp][] = [
    ["let x = Zero()\nprint x;", 15, /expected `;`, found keyword `print`/],
    ["let x = ();", 9, /expected an expression, found `\)`/],
    ["mutual { }", 9, /mutual/],
    ["mutual { data A() : Type() {} fn f() -> (r : A()) { r } }", 30, /either `data` declarations or functions/],
    ["let x = Zero(); -- caf\u00e9\n", 22, /non-ASCII/],
    ["let x = Zer\u00f6();", 11, /non-ASCII/],
    ["fn _(n : Nat()) -> (r : Nat()) { n }", 3, /expected a name, found `_`/],
    ["fn match(n : Nat()) -> (r : Nat()) { n }", 3, /keyword `match`/],
    ["let print = Zero();", 4, /keyword `print`/],
    ["data D(x is Zero()) : Type() {}", 9, /expected `:`/],
    ["data D() : Nat() {}", 11, /`Type`/],
    ["fn f() -> () { x }", 11, /a name or `_`/],
    ["fn f() { x }", 7, /`->`/],
    ["let x = 1;", 8, /starts with a letter/],
    ["let x = _a;", 8, /starts with a letter/],
    ["let x = a - b;", 10, /unexpected character/],
    ["let x = { comptime let C() = y; z };", 10, /an expression/],
    ["let x = f(_);", 10, /an expression/],
    ["let x = { y; }", 11, /expected `}`/],
    ["x;", 0, /a declaration or a top-level statement/],
  ];
  for (const [source, start, message] of cases) {
    const e = err(source);
    assert.match(e.message, message, source);
    assert.equal(e.start, start, source);
  }
});

test("the first error is reported", () => {
  assert.match(err("let x = ;\n\u00e9").message, /expected an expression/);
  assert.match(err("let x = y;\n\u00e9 let").message, /non-ASCII/);
});

test("erased and many are names in phase 1 and keywords in phase 2", () => {
  assert.deepEqual(strip(ok("let erased = many;").tops[0]), { kind: "let", binders: [{ name: id("erased"), ann: null, mult: null }], rhs: variable("many") });
  assert.match(err("let x = many;", 2).message, /expected an expression, found keyword `many`/);
  assert.match(err("let erased = x;", 2).message, /expected a name or `_`, found `=`/);
  ok("fn erased(many : Nat()) -> (r : Nat()) { many }");
  assert.match(err("fn f(erased n : Nat()) -> (r : Nat()) { n }").message, /expected `:` or `is`/);
});

test("phase 2 multiplicities", () => {
  const program = ok(`${nat}
data V(n : Nat()) : Type() { C(erased n : Nat(), many x : Nat()) : V(n); }
fn f(subterm erased n : Nat(), v : V(n)) -> (erased m : Nat(), r : Nat()) {
  let erased C(k, x) = v;
  let (erased a : Nat(), many b) = match erased v : (erased s : Nat(), t : Nat()) { C(j, y) => (j, y); };
  let erased c = a;
  (c, b)
}
comptime let erased C(_, z) = C(Zero(), Zero());
let w = f(_, C(_, Zero()));
`, 2);
  const [, data, fn, comptimeLet, call] = program.tops;
  assert.ok(data?.kind === "data" && fn?.kind === "fn");
  assert.deepEqual(data.ctors[0]?.fields.map(b => b.mult), ["erased", "many"]);
  assert.deepEqual(fn.params.map(p => [p.subterm, p.mult]), [[true, "erased"], [false, null]]);
  assert.deepEqual(fn.returns.map(b => b.mult), ["erased", null]);
  const [patlet, tuple, single] = fn.body.stmts;
  assert.ok(patlet?.kind === "patlet" && tuple?.kind === "let" && single?.kind === "let");
  assert.equal(patlet.mult, "erased");
  assert.deepEqual(tuple.binders.map(b => b.mult), ["erased", "many"]);
  assert.ok(tuple.rhs.kind === "match" && tuple.rhs.ann !== "_");
  assert.equal(tuple.rhs.mult, "erased");
  assert.deepEqual(tuple.rhs.ann.map(b => b.mult), ["erased", null]);
  assert.deepEqual(single.binders.map(b => [b.name.name, b.mult]), [["c", "erased"]]);
  assert.ok(comptimeLet?.kind === "patlet");
  assert.deepEqual([comptimeLet.comptime, comptimeLet.mult], [true, "erased"]);
  assert.deepEqual(strip(call), { kind: "let", binders: [{ name: id("w"), ann: null, mult: null }], rhs: app("f", variable(null), app("C", variable(null), app("Zero"))) });
  assert.match(err("data D(erased n : Type()) : Type() {}", 2).message, /keyword `erased`/);
  assert.match(err("let x = sorry(erased y : Type());", 2).message, /keyword `erased`/);
  assert.match(err("let erased (x) = y;", 2).message, /a name or `_`/);
  assert.match(err("let x = (_);", 2).message, /an expression/);
});

test("function goals", () => {
  const binder = (name: string | null, head: string, mult: string | null = null) => ({ name: id(name), ann: { kind: "type", term: term(head) }, mult });
  assert.deepEqual(strip(ok("goal fn (subterm n : Nat(), _ : Nat()) -> (r : Nat()); qed f;").tops), [
    { kind: "goal", type: { params: [{ ...binder("n", "Nat"), subterm: true }, { ...binder(null, "Nat"), subterm: false }], returns: [binder("r", "Nat")] } },
    { kind: "qed", expr: variable("f") },
  ]);
  assert.deepEqual(strip(ok("goal fn () -> (erased r : Nat());", 2).tops[0]), { kind: "goal", type: { params: [], returns: [binder("r", "Nat", "erased")] } });
  const cases: [string, number, RegExp][] = [
    ["goal fn f(n : Nat()) -> (r : Nat());", 8, /expected `\(`, found `f`/],
    ["goal fn (n : Nat()) (r : Nat());", 20, /expected `->`/],
    ["goal fn (n : Nat()) -> (r : Nat()) { n }", 35, /expected `;`, found `\{`/],
    ["goal fn (n : Nat()) -> ();", 24, /a name or `_`/],
  ];
  for (const [source, start, message] of cases) {
    const e = err(source);
    assert.match(e.message, message, source);
    assert.equal(e.start, start, source);
  }
});
