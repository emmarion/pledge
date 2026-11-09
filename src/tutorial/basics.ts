import type { Section } from "./pages.ts";
import { nat, vec } from "../examples.ts";
import { paragraphs, box, evenOdd, plusFn } from "./programs.ts";

const bool = `data Bool() : Type() {
  True() : Bool();
  False() : Bool();
}`;

const twoVec = `let one = Succ(Zero());
let xs = VCons(Nat(), one, Zero(),
  VCons(Nat(), Zero(), one, VNil(Nat())));`;

const twoThenThree = (rest: string): string => `let two = Succ(Succ(Zero()));
print two;
${rest}`;

const isZeroFn = (succBranch: string): string => `fn isZero(n : Nat()) -> (b : Bool()) {
  match n : (b : Bool()) {
    Zero() => True();${succBranch}
  }
}
print isZero(Succ(Zero()));
`;

const assertion = (comment: string, term: string): string => `let one = Succ(Zero());
let two = Succ(one);
inspect;
${comment}let y is ${term} = two;
`;

const vheadWith = (branch: string): string => `fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  match v : (x : A) {${branch}
  }
}`;

const vhead = vheadWith(`
    VCons(_, _, hd, _) => hd;`);

const vheadUse = (fn: string): string => `${fn}
let v = VCons(Nat(), Zero(), Succ(Zero()), VNil(Nat()));
print vhead(Nat(), Zero(), v);
`;

const vuncons = (body: string, use: string): string => `fn vuncons(A : Type(), n : Nat(), v : Vec(A, Succ(n)))
    -> (hd : A, tl : Vec(A, n)) {
  match v : (hd : A, tl : Vec(A, n)) {
    VCons(_, _, h, t) => ${body};
  }
}
${use}
`;

const cons = (m: string): string => `fn cons(A : Type(), n : Nat(), x : A, v : Vec(A, n))
    -> (${m}, w : Vec(A, m)) {
  (Succ(n), VCons(A, n, x, v))
}
let (m, w) = cons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), w);
`;

const vsecond = (rest: string): string => `fn vsecond(A : Type(), n : Nat(), v : Vec(A, Succ(Succ(n))))
    -> (x : A) {
  let VCons(_, _, _, rest) = v;
  ${rest}
}
print vsecond(Nat(), Zero(), xs);
`;

const isEvenOdd = (succBranch: string, proof: string): string => `mutual {
  fn isEven(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => True();
      Succ(m) => isOdd(subterm m);
    }
  }
  fn isOdd(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => False();${succBranch}
    }
  }
}
print isEven(Succ(Succ(Zero())));
let p : Even(Succ(Succ(Zero())))${proof};
`;

const ack = `fn ack(subterm m : Nat(), subterm n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => Succ(n);
    Succ(m1) => match n : (r : Nat()) {
      Zero() => ack(subterm m1, Succ(Zero()));
      Succ(n1) => ack(subterm m1, ack(same m, subterm n1));
    };
  }
}`;

export const basics: Section = { title: "Basics", pages: [
  {
    slug: "nat",
    title: "Data and Nat()",
    phase: 1,
    prose: paragraphs(
      "Each page shows read-only boxes of source above your box, and checks them all as one program (§12). The panels beside the editor (below it on a narrow screen) describe the position of the caret: what is expected there, what is in scope, and more, as later pages show (§13). The status line under your box says whether the program checks, whether it contains `sorry`, and whether its goal is proved. An error is marked where it occurs.",
      "The read-only box below declares the data type constructor `Nat`, with two value constructors, `Zero` and `Succ` (§5). Every application is written with its parentheses, even with no arguments, so the type is `Nat()` and zero is `Zero()` (§1).",
      "`let x = e;` binds the name `x` to `e`'s result (§8). `print e;` evaluates `e` and shows its value beside the statement (§12)."),
    task: "Bind `three` to the number three and `print` it.",
    refs: "§1, §5, §8, §12, §13",
    boxes: [nat],
    initial: `-- Bind three to the number three, then print it.
${twoThenThree("")}`,
    requireQed: false,
    solution: twoThenThree(`let three = Succ(two);
print three;
`),
  },
  {
    slug: "functions",
    title: "Functions and match",
    phase: 1,
    prose: paragraphs(
      "A function names its parameters and its returns: `fn isZero(n : Nat()) -> (b : Bool())`. Its body is a block, `{ statements; final expression }` (§8).",
      "A `match` takes apart the value of an expression, its scrutinee, here `n`. It is annotated with the telescope it produces, a parenthesized list of binders (§1), here `(b : Bool())` (§10); `_` is allowed in its place where a whole telescope is given, as at a function body. Each value constructor of the scrutinee's type has one branch, unless it is refuted (a later page). Patterns do not nest: a branch names the fields of one value constructor.",
      "The program is rejected as it stands. Put the caret on the `match` and read the error and the Expected panel."),
    task: "Add the missing branch so that `isZero` returns `False()` for any `Succ`.",
    refs: "§1, §8, §10",
    boxes: [box(nat, bool)],
    initial: `-- Add the branch for Succ, returning False().
${isZeroFn("")}`,
    requireQed: false,
    solution: isZeroFn(`
    Succ(_) => False();`),
  },
  {
    slug: "knowledge",
    title: "What the checker knows",
    phase: 1,
    prose: paragraphs(
      "The checker keeps a scope of entries, each with a type and possibly an `is` rule (§7). After `let two = Succ(one);`, `two` names the entry of the application `Succ(one)`, whose rule is that it is `Succ(one)` (§7, §8). Put the caret on the last line and look at the Scope panel, which shows rules canonicalized (§13).",
      "Two types are compared by canonicalizing them, rewriting by the `is` rules to a fixed point, and then comparing for identity (§3, §7). Click a term, or press \"Explain the term at the caret\", to see its canonical form and the rewrites that produce it. The \"At the caret\" field checks a type or an expression you type, in the scope at the caret. `inspect;` reports the same panels beside the statement; click its disclosure.",
      "In `let y is e = e2;`, the binder `y is e` asserts a fact the checker must already know: `e2` must canonicalize to the same term as `e` (§6)."),
    task: "The assertion on the last line is wrong. Fix the term after `is` so that the line checks.",
    refs: "§3, §6, §7, §8, §13",
    boxes: [nat],
    initial: assertion("-- This assertion is wrong: fix the term after is.\n", "Succ(Zero())"),
    requireQed: false,
    solution: assertion("", "Succ(Succ(Zero()))"),
  },
  {
    slug: "vhead",
    title: "Dependent types: vhead",
    phase: 1,
    prose: paragraphs(
      "`Vec(A, n)` is a list of `n` values of type `A`: its type depends on a value. `VNil` and `VCons` each declare their own `A`, since a type constructor's parameters are in scope only in its own telescope (§5).",
      "`vhead` takes a `Vec(A, Succ(n))`, so it should need no branch for `VNil`. A match forces each value constructor (§7). Forcing `VNil` equates `v`'s type, `Vec(A, Succ(n))`, with `VNil`'s, `Vec(A1, Zero())` for a fresh field `A1`, and so `Succ(n)` with `Zero()`: applications of different value constructors. Forcing fails, so `VNil` is refuted, and a branch for it is an error (§10)."),
    task: "Give the match its one branch. Then put the caret on the `match` and open `VNil` in the Refutations panel to see the derivation.",
    refs: "§5, §7, §10",
    boxes: [box(nat, vec)],
    initial: `-- Give the match its branch for VCons.
${vheadUse(vheadWith(""))}`,
    requireQed: false,
    solution: vheadUse(vhead),
  },
  {
    slug: "vuncons",
    title: "Several results",
    phase: 1,
    prose: paragraphs(
      "A function can return several values, and a `match` can produce several: its annotation is a telescope (§8, §10). A tuple `(a, b)` produces one value per element, and a tuple `let`, `let (h, t) = e;`, binds them.",
      "Put the caret on the branch body: Expected shows what it is still to produce (§13)."),
    task: "Make the branch produce both the head and the tail, then bind both results of the call and print them.",
    refs: "§8, §10, §13",
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return both the head and the tail, then bind and print both.
${vuncons("h", `let h = vuncons(Nat(), one, xs);
print h;`)}`,
    requireQed: false,
    solution: vuncons("(h, t)", `let (h, t) = vuncons(Nat(), one, xs);
print h;
print t;`),
  },
  {
    slug: "is-binders",
    title: "is binders",
    phase: 1,
    prose: paragraphs(
      "The results of a call are new entries known only by their types (§7). Here `cons` returns `m : Nat()`, so after the call the checker knows nothing more about `m`, and `vhead` cannot accept `w : Vec(Nat(), m)`. Put the caret on the last line and look at `m` in the Scope panel.",
      "A return is allowed to be written `m is e` instead of `m : T` (§6). Its type is then the type of `e`. When the binder is opened, at a call's results, its entry gets the rule that it is `e`; when it is instantiated, as the body's result is checked against it, that result must canonicalize to `e`."),
    task: "Change `m`'s binder in `cons`'s returns so that the last line checks.",
    refs: "§6, §7",
    boxes: [box(nat, vec, vhead)],
    initial: `-- Change m : Nat() to an is binder, so that the last line checks.
${cons("m : Nat()")}`,
    requireQed: false,
    solution: cons("m is Succ(n)"),
  },
  {
    slug: "pattern-let",
    title: "Pattern let",
    phase: 1,
    prose: paragraphs(
      "A pattern `let`, such as `let VCons(_, _, h, t) = v;`, is a statement (§10). Exactly one value constructor of `v`'s type must survive forcing, and it must be the one written. Its names are in scope for the rest of the enclosing block; its fields and facts last longer, to the end of the enclosing match branch or function body, or of the program (§7, §10).",
      "Inside `vsecond`, `v` has type `Vec(A, Succ(Succ(n)))`, so the first pattern `let` gives a `rest` whose type canonicalizes to `Vec(A, Succ(n))`, and `VNil` is refuted again for `rest`. With `n : Nat()` alone, `let Succ(k) = n;` would be rejected, since `Zero` is not refuted."),
    task: "Finish `vsecond` with a second pattern `let`.",
    refs: "§7, §10",
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return v's second element, with a second pattern let on rest.
${vsecond("rest")}`,
    requireQed: false,
    solution: vsecond(`let VCons(_, _, y, _) = rest;
  y`),
  },
  {
    slug: "termination",
    title: "Termination: subterm and same",
    phase: 1,
    prose: paragraphs(
      "A body is allowed to call any function declared before it, with no annotation, and top-level code any function (§9). A call of a function to itself must decrease. In the simplest case a parameter is marked `subterm`, and the call marks its argument `subterm e`, where `e` must be a strict subterm of the caller's own `subterm` parameter. In `plus`'s `Succ(k)` branch, `m` canonicalizes to `Succ(k)`, so `k` is a strict subterm of `m`. The marks are always written; none is inferred.",
      "`ack` below has two `subterm` parameters. A call that decreases the second marks the argument for the first `same`, and that argument must be canonically identical to the caller's first. The Termination panel lists the enclosing function's `subterm` parameters (§13)."),
    task: "`plus` is rejected as written. Mark it so that it is accepted.",
    refs: "§9, §13",
    boxes: [box(nat, ack)],
    initial: `-- Mark the recursion so that plus is accepted.
${plusFn("")}
let two = Succ(Succ(Zero()));
print plus(two, ack(Succ(Zero()), two));
`,
    requireQed: false,
    solution: `${plusFn("subterm ")}
let two = Succ(Succ(Zero()));
print plus(two, ack(Succ(Zero()), two));
`,
  },
  {
    slug: "mutual",
    title: "Mutual groups: Even and Odd",
    phase: 1,
    prose: paragraphs(
      "Declarations that refer to each other are written together in a `mutual` block, their group (§5, §8). The data type constructors `Even` and `Odd` below form one; a value of `Even(n)` can be read as evidence that `n` is even.",
      "A function outside any `mutual` block is a group of its own. Functions of one group are allowed to call each other, under the same `subterm` rule as a function calling itself, and the Termination panel lists the enclosing function's group (§9, §13)."),
    task: "Give `isOdd` its `Succ` branch, calling `isEven`, then replace `EvenZero()` with a proof of `Even(Succ(Succ(Zero())))`.",
    refs: "§5, §8, §9, §13",
    boxes: [box(nat, bool, evenOdd)],
    initial: `-- Give isOdd a Succ branch calling isEven, then replace EvenZero()
-- with a proof of Even(Succ(Succ(Zero()))).
${isEvenOdd("", " = EvenZero()")}`,
    requireQed: false,
    solution: isEvenOdd(`
      Succ(m) => isEven(subterm m);`, `
  = EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()))`),
  },
] };
