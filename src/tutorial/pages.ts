import type { Phase } from "../syntax.ts";

export interface Page {
  slug: string;
  title: string;
  phase: Phase;
  prose: string;
  boxes: string[];
  initial: string;
  requireQed: boolean;
  solution: string;
}

const paragraphs = (...ps: string[]): string => ps.join("\n\n");
const box = (...parts: string[]): string => parts.join("\n\n");

const nat = `data Nat() : Type() {
  Zero() : Nat();
  Succ(pred : Nat()) : Nat();
}`;

const bool = `data Bool() : Type() {
  True() : Bool();
  False() : Bool();
}`;

const vec = `data Vec(A : Type(), n : Nat()) : Type() {
  VNil(A : Type()) : Vec(A, Zero());
  VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n))
    : Vec(A, Succ(n));
}`;

const twoVec = `let one = Succ(Zero());
let xs = VCons(Nat(), one, Zero(),
  VCons(Nat(), Zero(), one, VNil(Nat())));`;

const vhead = `fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  match v : (x : A) {
    VCons(_, _, hd, _) => hd;
  }
}`;

const evenOdd = `mutual {
  data Even(n : Nat()) : Type() {
    EvenZero() : Even(Zero());
    EvenSucc(n : Nat(), p : Odd(n)) : Even(Succ(n));
  }
  data Odd(n : Nat()) : Type() {
    OddSucc(n : Nat(), p : Even(n)) : Odd(Succ(n));
  }
}`;

const eq = `data Eq(A : Type(), x : A, y : A) : Type() {
  Refl(A : Type(), x : A) : Eq(A, x, x);
}`;

const falseType = `data False() : Type() {}`;

const isZero = `data IsZero(n : Nat()) : Type() {
  IsZeroHere() : IsZero(Zero());
}`;

const ack = `fn ack(subterm m : Nat(), subterm n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => Succ(n);
    Succ(m1) => match n : (r : Nat()) {
      Zero() => ack(subterm m1, Succ(Zero()));
      Succ(n1) => ack(subterm m1, ack(same m, subterm n1));
    };
  }
}`;

const plus = `data Plus(m : Nat(), n : Nat(), r : Nat()) : Type() {
  PlusZero(n : Nat()) : Plus(Zero(), n, n);
  PlusSucc(m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    : Plus(Succ(m), n, Succ(r));
}

fn plus(subterm m : Nat(), n : Nat())
    -> (r : Nat(), p : Plus(m, n, r)) {
  match m : _ {
    Zero() => (n, PlusZero(n));
    Succ(k) => {
      let (r, p) = plus(subterm k, n);
      (Succ(r), PlusSucc(k, n, r, p))
    };
  }
}`;

const option = `data Option(A : Type()) : Type() {
  None(A : Type()) : Option(A);
  Some(A : Type(), x : A) : Option(A);
}`;

const decideEven = `fn decideEvenRec(subterm n : Nat()) -> (r : Option(Even(n))) {
  match n : (r : Option(Even(n))) {
    Zero() => Some(Even(n), EvenZero());
    Succ(m) => match m : (r : Option(Even(n))) {
      Zero() => None(Even(n));
      Succ(k) => match decideEvenRec(subterm k) : _ {
        None(_) => None(Even(n));
        Some(_, q) => Some(Even(n), EvenSucc(m, OddSucc(k, q)));
      };
    };
  }
}

fn decideEven(n : Nat()) -> (r : Option(Even(n))) {
  decideEvenRec(n)
}`;

const four = `let four = Succ(Succ(Succ(Succ(Zero()))));
goal Even(four);`;

const fourIsEven = `EvenSucc(Succ(Succ(Succ(Zero()))),
  OddSucc(Succ(Succ(Zero())),
    EvenSucc(Succ(Zero()),
      OddSucc(Zero(), EvenZero()))))`;

export const pages: Page[] = [
  {
    slug: "nat",
    title: "Data and Nat()",
    phase: 1,
    prose: paragraphs(
      "This tutorial was written by a Claude session, not by Pledge's owner. DESIGN.md is the specification; where the two disagree, DESIGN.md is right and this tutorial is wrong. Section numbers (§) point to the DESIGN.md text a claim is based on.",
      "Each page shows read-only boxes of source above your box, and checks them all as one program (§12). The panels beside the editor (below it on a narrow screen) describe the position of the caret: what is expected there, what is in scope, and more, as later pages show (§13). The status line under your box says whether the program checks, whether it contains `sorry`, and whether its goal is proved. An error is marked where it occurs.",
      "The box above declares the data type constructor `Nat`, with two value constructors, `Zero` and `Succ` (§5). Every application is written with its parentheses, even with no arguments, so the type is `Nat()` and zero is `Zero()` (§1).",
      "`let x = e;` binds the name `x` to `e`'s result (§8). `print e;` evaluates `e` and shows its value beside the statement (§12).",
      "Task: bind `three` to the number three and `print` it."),
    boxes: [nat],
    initial: `-- Bind three to the number three, then print it.
let two = Succ(Succ(Zero()));
print two;
`,
    requireQed: false,
    solution: `let two = Succ(Succ(Zero()));
print two;
let three = Succ(two);
print three;
`,
  },
  {
    slug: "functions",
    title: "Functions and match",
    phase: 1,
    prose: paragraphs(
      "A function names its parameters and its returns: `fn isZero(n : Nat()) -> (b : Bool())`. Its body is a block, `{ statements; final expression }` (§8).",
      "A `match` is annotated with the telescope it produces, here `(b : Bool())` (§10); `_` is allowed in its place where a whole telescope is given, as at a function body. Each value constructor of the scrutinee's type has one branch, unless it is refuted (a later page). Patterns do not nest: a branch names the fields of one value constructor.",
      "The program is rejected as it stands. Put the caret on the `match` and read the error and the Expected panel.",
      "Task: add the missing branch so that `isZero` returns `False()` for any `Succ`."),
    boxes: [box(nat, bool)],
    initial: `-- Add the branch for Succ.
fn isZero(n : Nat()) -> (b : Bool()) {
  match n : (b : Bool()) {
    Zero() => True();
  }
}
print isZero(Succ(Zero()));
`,
    requireQed: false,
    solution: `fn isZero(n : Nat()) -> (b : Bool()) {
  match n : (b : Bool()) {
    Zero() => True();
    Succ(_) => False();
  }
}
print isZero(Succ(Zero()));
`,
  },
  {
    slug: "knowledge",
    title: "What the checker knows",
    phase: 1,
    prose: paragraphs(
      "The checker keeps a scope of entries, each with a type and possibly an `is` rule (§7). After `let two = Succ(one);`, `two` names the entry of the application `Succ(one)`, whose rule is that it is `Succ(one)` (§7, §8). Put the caret on the last line and look at the Scope panel, which shows rules canonicalized (§13).",
      "Two types are compared by canonicalizing them, rewriting by the `is` rules to a fixed point, and then comparing for identity (§3, §7). Click a term, or press \"Explain the term at the caret\", to see its canonical form and the rewrites that produce it. The \"At the caret\" field checks a type or an expression you type, in the scope at the caret. `inspect;` reports the same panels beside the statement; click its disclosure.",
      "A binder written `y is e` in a tuple `let` asserts a fact the checker must already know (§6).",
      "Task: the assertion on the last line is wrong. Fix it so that it checks."),
    boxes: [nat],
    initial: `let one = Succ(Zero());
let two = Succ(one);
inspect;
-- This assertion is wrong: fix it.
let y is Succ(Zero()) = two;
`,
    requireQed: false,
    solution: `let one = Succ(Zero());
let two = Succ(one);
inspect;
let y is Succ(Succ(Zero())) = two;
`,
  },
  {
    slug: "vhead",
    title: "Dependent types: vhead",
    phase: 1,
    prose: paragraphs(
      "`Vec(A, n)` is a list of `n` values of type `A`: its type depends on a value. `VNil` and `VCons` each declare their own `A`, since a type constructor's parameters are in scope only in its own telescope (§5).",
      "`vhead` takes a `Vec(A, Succ(n))`, so it should need no branch for `VNil`. A match forces each value constructor (§7). Forcing `VNil` equates `v`'s type, `Vec(A, Succ(n))`, with `VNil`'s, `Vec(A1, Zero())` for a fresh field `A1`, and so `Succ(n)` with `Zero()`: applications of different value constructors. Forcing fails, so `VNil` is refuted, and a branch for it is an error (§10).",
      "Task: give the match its one branch. Then put the caret on the `match` and open `VNil` in the Refutations panel to see the derivation."),
    boxes: [box(nat, vec)],
    initial: `-- Give the match its branch for VCons.
fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  match v : (x : A) {
  }
}
let v = VCons(Nat(), Zero(), Succ(Zero()), VNil(Nat()));
print vhead(Nat(), Zero(), v);
`,
    requireQed: false,
    solution: `fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  match v : (x : A) {
    VCons(_, _, hd, _) => hd;
  }
}
let v = VCons(Nat(), Zero(), Succ(Zero()), VNil(Nat()));
print vhead(Nat(), Zero(), v);
`,
  },
  {
    slug: "vuncons",
    title: "Several results",
    phase: 1,
    prose: paragraphs(
      "A function can return several values, and a `match` can produce several: its annotation is a telescope (§8, §10). A tuple `(a, b)` produces one value per element, and a tuple `let`, `let (h, t) = e;`, binds them.",
      "Put the caret on the branch body: Expected shows what it is still to produce (§13).",
      "Task: make the branch produce both the head and the tail, then bind both results of the call and print them."),
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return both the head and the tail, then bind and print both.
fn vuncons(A : Type(), n : Nat(), v : Vec(A, Succ(n)))
    -> (hd : A, tl : Vec(A, n)) {
  match v : (hd : A, tl : Vec(A, n)) {
    VCons(_, _, h, t) => h;
  }
}
let h = vuncons(Nat(), one, xs);
print h;
`,
    requireQed: false,
    solution: `fn vuncons(A : Type(), n : Nat(), v : Vec(A, Succ(n)))
    -> (hd : A, tl : Vec(A, n)) {
  match v : (hd : A, tl : Vec(A, n)) {
    VCons(_, _, h, t) => (h, t);
  }
}
let (h, t) = vuncons(Nat(), one, xs);
print h;
print t;
`,
  },
  {
    slug: "is-binders",
    title: "is binders",
    phase: 1,
    prose: paragraphs(
      "The results of a call are new entries known only by their types (§7). Here `cons` returns `m : Nat()`, so after the call the checker knows nothing more about `m`, and `vhead` cannot accept `w : Vec(Nat(), m)`. Put the caret on the last line and look at `m` in the Scope panel.",
      "A return is allowed to be written `m is e` instead of `m : T` (§6). Its type is then the type of `e`. When the binder is opened, at a call's results, its entry gets the rule that it is `e`; when it is instantiated, as the body's result is checked against it, that result must canonicalize to `e`.",
      "Task: change `m`'s binder in `cons`'s returns so that the last line checks."),
    boxes: [box(nat, vec, vhead)],
    initial: `-- Change m's binder so that the last line checks.
fn cons(A : Type(), n : Nat(), x : A, v : Vec(A, n))
    -> (m : Nat(), w : Vec(A, m)) {
  (Succ(n), VCons(A, n, x, v))
}
let (m, w) = cons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), w);
`,
    requireQed: false,
    solution: `fn cons(A : Type(), n : Nat(), x : A, v : Vec(A, n))
    -> (m is Succ(n), w : Vec(A, m)) {
  (Succ(n), VCons(A, n, x, v))
}
let (m, w) = cons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), w);
`,
  },
  {
    slug: "pattern-let",
    title: "Pattern let",
    phase: 1,
    prose: paragraphs(
      "A pattern `let`, such as `let VCons(_, _, h, t) = v;`, is a statement (§10). Exactly one value constructor of `v`'s type must survive forcing, and it must be the one written. Its fields and facts stay in scope to the end of the enclosing block.",
      "Inside `vsecond`, `v` has type `Vec(A, Succ(Succ(n)))`, so the first pattern `let` gives a `rest` whose type canonicalizes to `Vec(A, Succ(n))`, and `VNil` is refuted again for `rest`. With `n : Nat()` alone, `let Succ(k) = n;` would be rejected, since `Zero` is not refuted.",
      "Task: finish `vsecond` with a second pattern `let`."),
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return the second element of v.
fn vsecond(A : Type(), n : Nat(), v : Vec(A, Succ(Succ(n))))
    -> (x : A) {
  let VCons(_, _, _, rest) = v;
  rest
}
print vsecond(Nat(), Zero(), xs);
`,
    requireQed: false,
    solution: `fn vsecond(A : Type(), n : Nat(), v : Vec(A, Succ(Succ(n))))
    -> (x : A) {
  let VCons(_, _, _, rest) = v;
  let VCons(_, _, y, _) = rest;
  y
}
print vsecond(Nat(), Zero(), xs);
`,
  },
  {
    slug: "termination",
    title: "Termination: subterm and same",
    phase: 1,
    prose: paragraphs(
      "A body is allowed to call any function of an earlier group with no annotation, and top-level code any function (§9). A call within the function's own group, such as a call to itself, must decrease. In the simplest case a parameter is marked `subterm`, and the call marks its argument `subterm e`, where `e` must be a strict subterm of the caller's own `subterm` parameter. In `plus`'s `Succ(k)` branch, `m` canonicalizes to `Succ(k)`, so `k` is a strict subterm of `m`. The marks are always written; none is inferred.",
      "`ack` above has two `subterm` parameters. A call that decreases the second marks the argument for the first `same`, and that argument must be canonically identical to the caller's first. The Termination panel lists the enclosing function's `subterm` parameters and the functions of its group (§13).",
      "Task: `plus` is rejected as written. Mark it so that it is accepted."),
    boxes: [box(nat, ack)],
    initial: `-- Mark the recursion so that plus is accepted.
fn plus(m : Nat(), n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => n;
    Succ(k) => Succ(plus(k, n));
  }
}
let two = Succ(Succ(Zero()));
print plus(two, ack(Succ(Zero()), two));
`,
    requireQed: false,
    solution: `fn plus(subterm m : Nat(), n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => n;
    Succ(k) => Succ(plus(subterm k, n));
  }
}
let two = Succ(Succ(Zero()));
print plus(two, ack(Succ(Zero()), two));
`,
  },
  {
    slug: "mutual",
    title: "Mutual groups: Even and Odd",
    phase: 1,
    prose: paragraphs(
      "Declarations that refer to each other are written together in a `mutual` block, their group (§5, §8). The data type constructors `Even` and `Odd` above form one; a value of `Even(n)` can be read as evidence that `n` is even.",
      "Functions of one group are allowed to call each other, under the same `subterm` rule as a function calling itself (§9).",
      "Task: finish `isOdd`, then replace `EvenZero()` with evidence that two is even."),
    boxes: [box(nat, bool, evenOdd)],
    initial: `-- Finish isOdd, then give real evidence that two is even.
mutual {
  fn isEven(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => True();
      Succ(m) => isOdd(subterm m);
    }
  }
  fn isOdd(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => False();
    }
  }
}
print isEven(Succ(Succ(Zero())));
let p : Even(Succ(Succ(Zero()))) = EvenZero();
`,
    requireQed: false,
    solution: `mutual {
  fn isEven(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => True();
      Succ(m) => isOdd(subterm m);
    }
  }
  fn isOdd(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => False();
      Succ(m) => isEven(subterm m);
    }
  }
}
print isEven(Succ(Succ(Zero())));
let p : Even(Succ(Succ(Zero())))
  = EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()));
`,
  },
  {
    slug: "equality",
    title: "Propositions as types: equality",
    phase: 1,
    prose: paragraphs(
      "A type can be read as a proposition and a value of it as a proof. The data type constructor `Eq` above has one value constructor, `Refl(A, x) : Eq(A, x, x)`, so, `sorry` aside, a value of `Eq(A, x, y)` is built only by `Refl`, whose type has the same `x` on both sides.",
      "`goal T;` sets the program's goal and `qed e;` checks `e` against it (§12). The status line reports whether the `qed` checks and whether the goal is proved. On this page the `qed` must be in your box.",
      "Task: prove the goal. Since `two` canonicalizes to `Succ(Succ(Zero()))`, one `Refl` should do."),
    boxes: [box(nat, eq), `let one = Succ(Zero());
let two = Succ(one);
goal Eq(Nat(), two, Succ(Succ(Zero())));`],
    initial: `-- Prove the goal with qed.
`,
    requireQed: true,
    solution: `qed Refl(Nat(), two);
`,
  },
  {
    slug: "plus-zero",
    title: "Proof by recursion",
    phase: 1,
    prose: paragraphs(
      "Types never contain function calls (§3), so `Eq(Nat(), plus(n, Zero()), n)` cannot be written. Here `plus` instead returns, beside its result `r`, a value of the data type `Plus(m, n, r)`, read as a proof that `m` plus `n` is `r`. `sum` is a call's result, known only by its type (§7), so `Refl(Nat(), two)` does not prove the goal.",
      "`plusZero`, by recursion on `n`, turns a proof of `Plus(n, Zero(), r)` into one of `Eq(Nat(), r, n)`. Matching on a value of `Eq` forces `Refl`, which equates the two sides of the `Eq` (§7): in that branch they canonicalize to the same term.",
      "Task: add the `PlusSucc` branch. In it, `n` canonicalizes to `Succ(m)` for the branch's first field `m`: call `plusZero(subterm m, ...)` on the inner proof and match on the `Eq` it returns. Then prove the goal."),
    boxes: [box(nat, eq, plus), `let two = Succ(Succ(Zero()));
let (sum, proof) = plus(two, Zero());
print sum;
goal Eq(Nat(), sum, two);`],
    initial: `-- Add the PlusSucc branch, then prove the goal with qed.
fn plusZero(subterm n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
    -> (e : Eq(Nat(), r, n)) {
  match p : _ {
    PlusZero(_) => Refl(Nat(), r);
  }
}
`,
    requireQed: true,
    solution: `fn plusZero(subterm n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
    -> (e : Eq(Nat(), r, n)) {
  match p : _ {
    PlusZero(_) => Refl(Nat(), r);
    PlusSucc(m, _, r1, q) => match plusZero(subterm m, r1, q) : _ {
      Refl(_, _) => Refl(Nat(), r);
    };
  }
}
qed plusZero(two, sum, proof);
`,
  },
  {
    slug: "empty",
    title: "Empty types and False()",
    phase: 1,
    prose: paragraphs(
      "`False` here is a data type constructor that declares no value constructors, unrelated to the value constructor `False` of `Bool` on earlier pages. A match on a value of `False()` has no branches, so its annotation can be any telescope, as `absurd` shows (§10).",
      "A function returning `False()` can be read as a proof that its parameters' types cannot all have values. SOUNDNESS.md, an argument that is not machine-checked, argues that in an accepted program without `sorry`, no `qed` proves `False()`: the `qed`'s expression would evaluate to a value of `False()`, which only a value constructor of `False` could build, and there is none.",
      "Task: show that `Zero()` and `Succ(Zero())` are not equal. The branch for `Refl` is an error, because `Refl` is refuted; open it under Refutations to see why."),
    boxes: [box(nat, eq, falseType), `fn absurd(f : False()) -> (n : Nat()) {
  match f : (n : Nat()) {}
}`],
    initial: `-- Make the match on e have no branches.
fn zeroNotOne(e : Eq(Nat(), Zero(), Succ(Zero())))
    -> (f : False()) {
  match e : (f : False()) {
    Refl(_, x) => x;
  }
}
`,
    requireQed: false,
    solution: `fn zeroNotOne(e : Eq(Nat(), Zero(), Succ(Zero())))
    -> (f : False()) {
  match e : (f : False()) {}
}
`,
  },
  {
    slug: "iszero",
    title: "Refuting through a proof",
    phase: 1,
    prose: paragraphs(
      "A value constructor is refuted only by what is known about the scrutinee and its type (§10). In `f`, `p : IsZero(n)` rules out `Succ` for `n`, but does not refute it, so the match on `n` still needs a `Succ` branch.",
      "In that branch, `p : IsZero(Succ(m))`, while `IsZeroHere()` has type `IsZero(Zero())`. So a match on `p` there refutes `IsZeroHere` and has no branches.",
      "Task: add the `Succ` branch."),
    boxes: [box(nat, isZero)],
    initial: `-- Add the Succ branch: match on p there.
fn f(n : Nat(), p : IsZero(n)) -> (r : Nat()) {
  match n : (r : Nat()) {
    Zero() => Zero();
  }
}
`,
    requireQed: false,
    solution: `fn f(n : Nat(), p : IsZero(n)) -> (r : Nat()) {
  match n : (r : Nat()) {
    Zero() => Zero();
    Succ(m) => match p : (r : Nat()) {};
  }
}
`,
  },
  {
    slug: "sorry",
    title: "sorry and taint",
    phase: 1,
    prose: paragraphs(
      "`sorry(telescope)` produces one new entry per entry of its telescope, with the type or `is` rule written there, and nothing behind it (§12). Checking goes on past it, so you can try out the rest of a proof first, but any use of `sorry` is unsound.",
      "Taint tracks what relies on a `sorry`: roughly, its results and what is built from them; §12 gives the rules. An expression whose results are all tainted is removed before evaluation, so `print p;` shows `sorry`, and a `qed` of a tainted result checks without proving the goal. Look at the status line: it says the program contains `sorry`, the `qed` checks, and the goal is not proved.",
      "Task: replace the `sorry` with real evidence that four is even."),
    boxes: [box(nat, evenOdd), four],
    initial: `-- Replace sorry with evidence that four is even.
let p = sorry(_ : Even(four));
print p;
qed p;
`,
    requireQed: true,
    solution: `let p = ${fourIsEven};
print p;
qed p;
`,
  },
  {
    slug: "comptime",
    title: "Proof by reflection",
    phase: 1,
    prose: paragraphs(
      "`decideEven(n)` returns `Some` of a proof of `Even(n)` when `n` is even, and `None` otherwise. A plain pattern `let` on its result is rejected: the checker knows the result only by its type, so forcing does not refute `None` (§7, §10).",
      "`comptime let Some(_, p) = e;` evaluates `e` during checking and requires its value to be headed by `Some`; the run, not forcing, rules out `None` (§11). It is written only at the top level.",
      "Task: make the `let` a `comptime` pattern `let`. Then try `decideEven` on three, `Succ(Succ(Succ(Zero())))`, and read the error, which shows the value (§11)."),
    boxes: [box(nat, evenOdd, option, decideEven), four],
    initial: `-- Make this a comptime pattern let.
let Some(_, p) = decideEven(four);
qed p;
`,
    requireQed: true,
    solution: `comptime let Some(_, p) = decideEven(four);
qed p;
`,
  },
  {
    slug: "soundness",
    title: "Why Pledge appears sound",
    phase: 1,
    prose: paragraphs(
      "Pledge has `Type() : Type()` and no universe hierarchy (§3). SOUNDNESS.md, a written argument by a Claude session that is not machine-checked, says the usual paradoxes seem not to reach Pledge: types never compute, since a type contains no call; termination comes from definition order and `subterm` parameters, not from types; functions are not first class, so no type mentions one; and whether a value has a type is decided by recursion on the value. It notes that Curry's paradox, and Girard's in Hurkens' form, seem to need function types over `Type()`, which cannot be written.",
      "`loop` in your box tries to prove `False()` by calling itself, and is rejected by the termination rule (§9). Try other ways if you like: passing a function as an argument, or writing a call in a type.",
      "Task: make the program check. The only way this tutorial knows is `sorry`, and then the status line reports that the program contains `sorry` and that the goal is not proved."),
    boxes: [box(nat, falseType), "goal False();"],
    initial: `-- Make this check. Can you prove the goal?
fn loop(n : Nat()) -> (f : False()) {
  loop(n)
}
qed loop(Zero());
`,
    requireQed: true,
    solution: `fn loop(n : Nat()) -> (f : False()) {
  sorry(_)
}
qed loop(Zero());
`,
  },
];
