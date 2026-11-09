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

const vecBy = (mult: string): string => `data Vec(A : Type(), n : Nat()) : Type() {
  VNil(${mult}A : Type()) : Vec(A, Zero());
  VCons(${mult}A : Type(), ${mult}n : Nat(), head : A, rest : Vec(A, n))
    : Vec(A, Succ(n));
}`;

const vec = vecBy("");

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

const isZeroEq = (succBranch: string): string => `fn f(n : Nat(), p : IsZero(n)) -> (e : Eq(Nat(), n, Zero())) {
  match n : _ {
    Zero() => Refl(Nat(), n);${succBranch}
  }
}
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

const plusFn = (mark: string): string => `fn plus(${mark}m : Nat(), n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => n;
    Succ(k) => Succ(plus(${mark}k, n));
  }
}`;

const plusRel = `data Plus(m : Nat(), n : Nat(), r : Nat()) : Type() {
  PlusZero(n : Nat()) : Plus(Zero(), n, n);
  PlusSucc(m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    : Plus(Succ(m), n, Succ(r));
}`;

const plus = box(plusRel, `fn plus(subterm m : Nat(), n : Nat())
    -> (r : Nat(), p : Plus(m, n, r)) {
  match m : _ {
    Zero() => (n, PlusZero(n));
    Succ(k) => {
      let (r, p) = plus(subterm k, n);
      (Succ(r), PlusSucc(k, n, r, p))
    };
  }
}`);

const times = `data Times(m : Nat(), n : Nat(), r : Nat()) : Type() {
  TimesZero(n : Nat()) : Times(Zero(), n, Zero());
  TimesSucc(m : Nat(), n : Nat(), r : Nat(), s : Nat(),
      t : Times(m, n, r), p : Plus(r, n, s)) : Times(Succ(m), n, s);
}`;

const plusZeroRight = `fn plusZeroRight(subterm n : Nat()) -> (p : Plus(n, Zero(), n)) {
  match n : _ {
    Zero() => PlusZero(Zero());
    Succ(k) => PlusSucc(k, Zero(), k, plusZeroRight(subterm k));
  }
}`;

const plusSuccHead = `fn plusSucc(m : Nat(), n : Nat(), r : Nat(), subterm p : Plus(m, n, r))
    -> (q : Plus(m, Succ(n), Succ(r))) {
  match p : _ {`;

const plusSucc = `${plusSuccHead}
    PlusZero(_) => PlusZero(Succ(n));
    PlusSucc(m1, _, r1, p1) =>
      PlusSucc(m1, Succ(n), Succ(r1), plusSucc(m1, n, r1, subterm p1));
  }
}`;

const plusCommHead = `fn plusComm(m : Nat(), n : Nat(), r : Nat(), subterm p : Plus(m, n, r))
    -> (q : Plus(n, m, r)) {
  match p : _ {`;

const plusComm = `${plusCommHead}
    PlusZero(_) => plusZeroRight(n);
    PlusSucc(m1, _, r1, p1) =>
      plusSucc(n, m1, r1, plusComm(m1, n, r1, subterm p1));
  }
}`;

const plusAssoc = (zeroBranch: string): string => `fn plusAssoc(a : Nat(), b : Nat(), c : Nat(), ab : Nat(), r : Nat(),
    subterm p : Plus(a, b, ab), q : Plus(ab, c, r))
    -> (bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(a, bc, r)) {
  match p : _ {
    ${zeroBranch}
    PlusSucc(a1, _, ab1, p1) => {
      let PlusSucc(_, _, r1, q3) = q;
      let (bc, s1, s2) = plusAssoc(a1, b, c, ab1, r1, subterm p1, q3);
      (bc, s1, PlusSucc(a1, bc, r1, s2))
    };
  }
}`;

const plusAssocRev = `fn plusAssocRev(a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), subterm q : Plus(a, bc, r))
    -> (ab : Nat(), q1 : Plus(a, b, ab), q2 : Plus(ab, c, r)) {
  match q : _ {
    PlusZero(_) => (b, PlusZero(b), p);
    PlusSucc(a1, _, r1, q3) => {
      let (ab1, s1, s2) = plusAssocRev(a1, b, c, bc, r1, p, subterm q3);
      (Succ(ab1), PlusSucc(a1, b, ab1, s1), PlusSucc(ab1, c, r1, s2))
    };
  }
}`;

const exchange = `fn exchange(w : Nat(), y : Nat(), x : Nat(), z : Nat(), wy : Nat(),
    xz : Nat(), r : Nat(), p : Plus(w, y, wy), q : Plus(x, z, xz),
    s : Plus(wy, xz, r))
    -> (wx : Nat(), yz : Nat(), p1 : Plus(w, x, wx),
        q1 : Plus(y, z, yz), s1 : Plus(wx, yz, r)) {
  let (yxz : Nat(), s2 : Plus(y, xz, yxz), s3 : Plus(w, yxz, r)) =
    plusAssoc(w, y, xz, wy, r, p, s);
  let (yx : Nat(), s4 : Plus(y, x, yx), s5 : Plus(yx, z, yxz)) =
    plusAssocRev(y, x, z, xz, yxz, q, s2);
  let (s6 : Plus(x, y, yx)) = plusComm(y, x, yx, s4);
  let (yz : Nat(), s7 : Plus(y, z, yz), s8 : Plus(x, yz, yxz)) =
    plusAssoc(x, y, z, yx, yxz, s6, s5);
  let (wx : Nat(), s9 : Plus(w, x, wx), s10 : Plus(wx, yz, r)) =
    plusAssocRev(w, x, yz, yxz, r, s8, s3);
  (wx, yz, s9, s7, s10)
}`;

const timesDistrib = (zeroBranch: string): string => `fn timesDistrib(a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), subterm t : Times(a, bc, r))
    -> (ab : Nat(), ac : Nat(), t1 : Times(a, b, ab),
        t2 : Times(a, c, ac), q : Plus(ab, ac, r)) {
  match t : _ {
    ${zeroBranch}
    TimesSucc(a1, _, r1, _, t3, p1) => {
      let (ab1, ac1, t4, t5, q1) =
        timesDistrib(a1, b, c, bc, r1, p, subterm t3);
      let (ab, ac, s1, s2, q2) =
        exchange(ab1, ac1, b, c, r1, bc, r, q1, p, p1);
      (ab, ac, TimesSucc(a1, b, ab1, ab, t4, s1),
        TimesSucc(a1, c, ac1, ac, t5, s2), q2)
    };
  }
}`;

const plusSuccGoal = `goal fn (m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    -> (q : Plus(m, Succ(n), Succ(r)));`;

const plusCommGoal = `goal fn (m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    -> (q : Plus(n, m, r));`;

const plusAssocGoal = `goal fn (a : Nat(), b : Nat(), c : Nat(), ab : Nat(), r : Nat(),
    p : Plus(a, b, ab), q : Plus(ab, c, r))
    -> (bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(a, bc, r));`;

const timesDistribGoal = `goal fn (a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), t : Times(a, bc, r))
    -> (ab : Nat(), ac : Nat(), t1 : Times(a, b, ab),
        t2 : Times(a, c, ac), q : Plus(ab, ac, r));`;

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

const hundred = box(plusFn("subterm "), `fn times(subterm m : Nat(), n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => Zero();
    Succ(k) => plus(times(subterm k, n), n);
  }
}`, `let five = Succ(Succ(Succ(Succ(Succ(Zero())))));
let ten = plus(five, five);
let n = times(ten, ten);
print n;
goal Even(n);`);

const four = `let four = Succ(Succ(Succ(Succ(Zero()))));
goal Even(four);`;

const fourIsEven = `EvenSucc(Succ(Succ(Succ(Zero()))),
  OddSucc(Succ(Succ(Zero())),
    EvenSucc(Succ(Zero()),
      OddSucc(Zero(), EvenZero()))))`;

const vecErased = vecBy("erased ");

const vheadBy = (mult: string): string => `fn vhead(${mult}A : Type(), ${mult}n : Nat(), v : Vec(A, Succ(n)))
    -> (x : A) {
  let VCons(_, _, hd, _) = v;
  hd
}`;

const vheadErased = vheadBy("erased ");

const eqErased = `data Eq(A : Type(), x : A, y : A) : Type() {
  Refl(erased A : Type(), erased x : A) : Eq(A, x, x);
}`;

const erasedUses = `fn vcons(erased A : Type(), erased n : Nat(), x : A, v : Vec(A, n))
    -> (w : Vec(A, Succ(n))) {
  VCons(A, n, x, v)
}
fn vsecond(erased A : Type(), erased n : Nat(),
    v : Vec(A, Succ(Succ(n)))) -> (x : A) {
  let VCons(_, _, _, rest) = v;
  vhead(A, n, rest)
}
let one = Succ(Zero());
let v = vcons(Nat(), one, Zero(),
  vcons(Nat(), Zero(), one, VNil(Nat())));
print vsecond(Nat(), Zero(), v);
print v;
`;

const len = (ret: string): string => `fn len(erased A : Type(), erased n : Nat(), v : Vec(A, n))
    -> (${ret}) {
  n
}
let v = VCons(Nat(), Zero(), Zero(), VNil(Nat()));
let erased k = len(Nat(), Succ(Zero()), v);
let (w : Vec(Nat(), k)) = v;
print w;
`;

const castHead = `fn cast(erased m : Nat(), erased n : Nat(),
    erased p : Eq(Nat(), m, n), v : Vec(Nat(), m))
    -> (w : Vec(Nat(), n)) {`;

const castUse = `print cast(_, _, Refl(_, Succ(Zero())), VCons(_, _, Zero(), VNil(_)));
qed cast;
`;

const pair = `fn pair(x : Nat()) -> (n : Nat(), v : Vec(Nat(), Succ(n))) {
  (Zero(), VCons(Nat(), Zero(), x, VNil(Nat())))
}`;

const escaped = `let (n, v) = pair(Succ(Zero()));
let h = { let VCons(_, _, hd, tl) = v; hd };
inspect;`;

const escapedGoal = "goal Eq(Vec(Nat(), Succ(n)), v, VCons(Nat(), n, h, t));";

const poisonedLet = (scrutinee: string): string => `let v = ${scrutinee};
let h = { let VCons(_, _, hd, _) = v; hd };
print n;
qed Refl(Nat(), n);
`;

const inBranch = `let (n, w) = pair(Zero());
goal Eq(Nat(), n, n);
let c = match n : (r : Nat()) {
  Zero() => Zero();
  Succ(k) => {
    let VCons(_, _, hd, _) = sorry(u : Vec(Nat(), n));
    hd
  };
};
print c;
print n;`;

const throughBlock = (a: string, n: string): string => `print vhead(${a}, ${n}, { v });
print vhead(${a}, ${n}, { let w = v; w });
`;

const taintedHole = (a: string): string => `let A = ${a};
fn count(v : Vec(A, Zero())) -> (r : Nat()) {
  Zero()
}
print count(VNil(_));
qed count(VNil(_));
`;

const succEq = (ret: string): string => `goal fn (a : Nat(), b is Succ(a)) -> (e : Eq(Nat(), b, Succ(a)));
fn succEq(subterm x : Nat(), y is Succ(x))
    -> (e : Eq(Nat(), ${ret})) {
  Refl(Nat(), y)
}
qed succEq;
`;

const absurdHead = `fn f(erased n : Nat(), p : IsZero(n)) -> (r : Nat()) {
  match erased n : (r : Nat()) {
    Zero() => Zero();`;

const absurdUse = `  }
}
print f(Zero(), IsZeroHere());
`;

export const disclaimer = "This tutorial was written by a Claude session, not by Pledge's owner. DESIGN.md is the specification; where the two disagree, DESIGN.md is right and this tutorial is wrong. Section numbers (§) point to the DESIGN.md text a claim is based on.";

export const pages: Page[] = [
  {
    slug: "nat",
    title: "Data and Nat()",
    phase: 1,
    prose: paragraphs(
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
    initial: `-- Add the branch for Succ, returning False().
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
      "In `let y is e = e2;`, the binder `y is e` asserts a fact the checker must already know: `e2` must canonicalize to the same term as `e` (§6).",
      "Task: the assertion on the last line is wrong. Fix the term after `is` so that the line checks."),
    boxes: [nat],
    initial: `let one = Succ(Zero());
let two = Succ(one);
inspect;
-- This assertion is wrong: fix the term after is.
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
    initial: `-- Change m : Nat() to an is binder, so that the last line checks.
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
      "A pattern `let`, such as `let VCons(_, _, h, t) = v;`, is a statement (§10). Exactly one value constructor of `v`'s type must survive forcing, and it must be the one written. Its names are in scope for the rest of the enclosing block; its fields and facts last longer, to the end of the enclosing match branch or function body, or of the program (§7, §10).",
      "Inside `vsecond`, `v` has type `Vec(A, Succ(Succ(n)))`, so the first pattern `let` gives a `rest` whose type canonicalizes to `Vec(A, Succ(n))`, and `VNil` is refuted again for `rest`. With `n : Nat()` alone, `let Succ(k) = n;` would be rejected, since `Zero` is not refuted.",
      "Task: finish `vsecond` with a second pattern `let`."),
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return v's second element, with a second pattern let on rest.
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
      "A body is allowed to call any function declared before it, with no annotation, and top-level code any function (§9). A call of a function to itself must decrease. In the simplest case a parameter is marked `subterm`, and the call marks its argument `subterm e`, where `e` must be a strict subterm of the caller's own `subterm` parameter. In `plus`'s `Succ(k)` branch, `m` canonicalizes to `Succ(k)`, so `k` is a strict subterm of `m`. The marks are always written; none is inferred.",
      "`ack` above has two `subterm` parameters. A call that decreases the second marks the argument for the first `same`, and that argument must be canonically identical to the caller's first. The Termination panel lists the enclosing function's `subterm` parameters (§13).",
      "Task: `plus` is rejected as written. Mark it so that it is accepted."),
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
      "Declarations that refer to each other are written together in a `mutual` block, their group (§5, §8). The data type constructors `Even` and `Odd` above form one; a value of `Even(n)` can be read as evidence that `n` is even.",
      "A function outside any `mutual` block is a group of its own. Functions of one group are allowed to call each other, under the same `subterm` rule as a function calling itself, and the Termination panel lists the enclosing function's group (§9, §13).",
      "Task: give `isOdd` its `Succ` branch, calling `isEven`, then replace `EvenZero()` with a proof of `Even(Succ(Succ(Zero())))`."),
    boxes: [box(nat, bool, evenOdd)],
    initial: `-- Give isOdd a Succ branch calling isEven, then replace EvenZero()
-- with a proof of Even(Succ(Succ(Zero()))).
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
      "A type can be read as a proposition and a value of it as a proof. The data type constructor `Eq` above has one value constructor, `Refl(A, x) : Eq(A, x, x)`, so, `sorry` (a later page) aside, a value of `Eq(A, x, y)` is built only by `Refl`, whose type has the same `x` on both sides.",
      "`goal T;` sets the program's goal and `qed e;` checks `e` against it (§12). The status line reports whether the `qed` checks and whether the goal is proved. On this page the `qed` must be in your box.",
      "Task: prove the goal. Since `two` canonicalizes to `Succ(Succ(Zero()))`, one `Refl` should do."),
    boxes: [box(nat, eq), `let one = Succ(Zero());
let two = Succ(one);
goal Eq(Nat(), two, Succ(Succ(Zero())));`],
    initial: `-- Prove the goal: write qed and one Refl.
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
      "Types never contain function calls (§3), so `Eq(Nat(), plus(n, Zero()), n)` cannot be written. Here `plus` instead returns, beside its result `r`, a value of the data type `Plus(m, n, r)`, read as a proof that `m` plus `n` is `r`.",
      "The goal on this page is a function goal (§12): the parameters and returns of a function, with no name and no body, read as: for every `n` and `r`, a proof of `Plus(n, Zero(), r)` gives a proof of `Eq(Nat(), r, n)`. `qed plusZero;` names a function, and checks when `plusZero`'s parameters and returns are canonically identical to the goal's, position by position, binder names aside; `subterm` marks are not compared, so `plusZero` is allowed to mark `n` `subterm` (§12). Nothing is passed or returned, so functions are still not first class (§4).",
      "`plusZero`, by recursion on `n`, turns a proof of `Plus(n, Zero(), r)` into one of `Eq(Nat(), r, n)`. Matching on a value of `Eq` forces `Refl`, which equates the two sides of the `Eq` (§7): in that branch they canonicalize to the same term.",
      "Task: add the `PlusSucc` branch. In it, `n` canonicalizes to `Succ(m)` for the branch's first field `m`: call `plusZero(subterm m, ...)` on the inner proof and match on the `Eq` it returns. Then prove the goal with `qed plusZero;`."),
    boxes: [box(nat, eq, plus), `goal fn (n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
    -> (e : Eq(Nat(), r, n));`],
    initial: `-- Add the PlusSucc branch, then prove the goal with qed plusZero;
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
qed plusZero;
`,
  },
  {
    slug: "plus-succ",
    title: "A lemma about Plus",
    phase: 1,
    prose: paragraphs(
      "The next pages prove facts about addition, stated with the data type constructor `Plus` from the previous page: `Plus(m, n, r)` is read as \"`m` plus `n` is `r`\". Its value constructors follow addition by recursion on the first argument: `PlusZero(n)` proves that zero plus `n` is `n`, and `PlusSucc(m, n, r, p)` turns a proof `p` that `m` plus `n` is `r` into one that `Succ(m)` plus `n` is `Succ(r)`. Each fact is a function goal, as on the previous page (§12): the parameters are the hypotheses, and the returns the conclusions.",
      "The goal here reads: if `m` plus `n` is `r`, then `m` plus `Succ(n)` is `Succ(r)`. A natural proof is an induction on `m`, written as a recursion on the proof `p`, marked `subterm`: in the `PlusSucc` branch, `p` canonicalizes to `PlusSucc` applied to the branch's fields, so the inner proof is a strict subterm of it (§9).",
      "The box above also shows `plusZeroRight`, which builds a proof that `n` plus zero is `n` by recursion on `n`. It is the previous page's fact in another form, producing the `Plus` proof rather than taking one apart. This page does not use it; the next one does.",
      "Task: write the two branches, then prove the goal with `qed plusSucc;`. Put the caret on each branch body: Scope shows what forcing the value constructor added, such as `m` being `Zero()` in the `PlusZero` branch, and Expected shows the type the branch is to produce. In the `PlusSucc(m1, _, r1, p1)` branch, a recursive call `plusSucc(m1, n, r1, subterm p1)` gives `Plus(m1, Succ(n), Succ(r1))`."),
    boxes: [box(nat, plusRel, plusZeroRight), plusSuccGoal],
    initial: `-- Write both branches, then prove the goal with qed plusSucc;
${plusSuccHead}
  }
}
`,
    requireQed: true,
    solution: `${plusSucc}
qed plusSucc;
`,
  },
  {
    slug: "plus-comm",
    title: "Commutativity of addition",
    phase: 1,
    prose: paragraphs(
      "The goal is commutativity: if `m` plus `n` is `r`, then `n` plus `m` is `r`. The proof is again an induction on `m`, as a recursion on `p`, and each branch needs one of the two lemmas above.",
      "In the `PlusZero` branch, `m` is `Zero()` and `r` is `n`, so the branch is to produce `Plus(n, Zero(), n)`. `Plus`'s value constructors follow its first argument, not its second, so none of them builds this directly for an unknown `n`; `plusZeroRight(n)` does, by its own induction on `n`.",
      "In the `PlusSucc(m1, _, r1, p1)` branch, `m` is `Succ(m1)`, `r` is `Succ(r1)` and `p1 : Plus(m1, n, r1)`. The recursive call `plusComm(m1, n, r1, subterm p1)` gives `Plus(n, m1, r1)`, and the branch is to produce `Plus(n, Succ(m1), Succ(r1))`: that is what `plusSucc` from the previous page gives, applied to `n`, `m1` and `r1`.",
      "Task: write both branches, checking each against the Expected and Scope panels, and prove the goal with `qed plusComm;`."),
    boxes: [box(nat, plusRel), box(plusZeroRight, plusSucc), plusCommGoal],
    initial: `-- Write both branches, then prove the goal with qed plusComm;
${plusCommHead}
  }
}
`,
    requireQed: true,
    solution: `${plusComm}
qed plusComm;
`,
  },
  {
    slug: "plus-assoc",
    title: "Associativity of addition",
    phase: 1,
    prose: paragraphs(
      "Associativity says that (a + b) + c and a + (b + c) are the same number. With `Plus`, every sum is named: from `p : Plus(a, b, ab)` and `q : Plus(ab, c, r)`, a proof of the goal produces a `bc` with `Plus(b, c, bc)` and `Plus(a, bc, r)`. A return such as `bc`, which later returns mention, can be read as \"there is a `bc` such that\".",
      "Your box holds a complete proof but for one branch. It is an induction on `a`, as a recursion on `p`. Put the caret on the last line of the `PlusSucc(a1, _, ab1, p1)` branch, `(bc, s1, PlusSucc(a1, bc, r1, s2))`. Scope shows the facts forcing `PlusSucc` added: `a` is `Succ(a1)`, `ab` is `Succ(ab1)`, and `p` is `PlusSucc(a1, b, ab1, p1)`. So `q`'s type canonicalizes to `Plus(Succ(ab1), c, r)`, `PlusZero` is refuted for `q`, and the pattern `let` on `q` is accepted (§10); after it, Scope shows that `r` is `Succ(r1)` and `q3 : Plus(ab1, c, r1)`.",
      "The recursive call marks `p1` `subterm`. With the caret in the body, Termination lists `p` as `plusAssoc`'s `subterm` parameter, and Scope shows that `p` canonicalizes to `PlusSucc(a1, b, ab1, p1)`, so `p1` is a strict subterm of it (§9). The call gives `bc`, `s1 : Plus(b, c, bc)` and `s2 : Plus(a1, bc, r1)`, and `PlusSucc` turns `s2` into the `Plus(Succ(a1), bc, Succ(r1))` that Expected asks for.",
      "Task: write the `PlusZero` branch where the comment is. There `a` is `Zero()` and `ab` is `b`, so `q : Plus(b, c, r)`; Expected shows what is left to choose. The `qed` is already in your box."),
    boxes: [box(nat, plusRel), plusAssocGoal],
    initial: `${plusAssoc("-- Write the PlusZero branch here.")}
qed plusAssoc;
`,
    requireQed: true,
    solution: `${plusAssoc("PlusZero(_) => (r, q, PlusZero(r));")}
qed plusAssoc;
`,
  },
  {
    slug: "times-distrib",
    title: "Distributivity of multiplication",
    phase: 1,
    prose: paragraphs(
      "`Times(m, n, r)` is read as \"`m` times `n` is `r`\"; like `Plus`'s, its value constructors follow its first argument: zero times `n` is zero, and if `m` times `n` is `r` and `r` plus `n` is `s`, then `Succ(m)` times `n` is `s`. The goal is left distributivity, a × (b + c) = a × b + a × c: from `Plus(b, c, bc)` and `Times(a, bc, r)`, a proof produces `ab` and `ac` with `Times(a, b, ab)`, `Times(a, c, ac)` and `Plus(ab, ac, r)`.",
      "The proof in your box is an induction on `a`, as a recursion on `t`. In the `TimesSucc` branch, Scope shows `t3 : Times(a1, bc, r1)` and `p1 : Plus(r1, bc, r)`, and the recursive call gives `ab1` and `ac1` with a1 × b = ab1, a1 × c = ac1 and ab1 + ac1 = r1. What is left is arithmetic on `Plus` alone: from (ab1 + ac1) + (b + c) = r, `exchange` produces `ab` and `ac` with ab1 + b = ab, ac1 + c = ac and ab + ac = r. The first two are the last fields `TimesSucc` needs to build `Times(Succ(a1), b, ab)` and `Times(Succ(a1), c, ac)`.",
      "`exchange` above, (w + y) + (x + z) = (w + x) + (y + z), has no recursion of its own: it chains associativity, read in both directions (`plusAssoc`, and `plusAssocRev`, proved by recursion on its second proof), and commutativity. Each `let` in it gives the type of every value it binds, and such a type can mention the binders before it in the same `let`, such as `yxz`; the checker checks each against the result the binder names. A binder referred to this way needs a type of its own, which is why `yxz` carries `: Nat()`: without one, the reference is an error. Put the caret on each line and compare Scope with these types.",
      "Task: write the `TimesZero` branch where the comment is. There `a` and `r` are `Zero()`; Expected shows what is to be produced."),
    boxes: [box(nat, plusRel, times), box(plusZeroRight, plusSucc, plusComm), box(plusAssoc("PlusZero(_) => (r, q, PlusZero(r));"), plusAssocRev), exchange, timesDistribGoal],
    initial: `${timesDistrib("-- Write the TimesZero branch here.")}
qed timesDistrib;
`,
    requireQed: true,
    solution: `${timesDistrib(`TimesZero(_) =>
      (Zero(), Zero(), TimesZero(b), TimesZero(c), PlusZero(Zero()));`)}
qed timesDistrib;
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
      "A value constructor is refuted only by what is known about the scrutinee and its type (§10). In `f`, `p : IsZero(n)` rules out `Succ` for `n`, but does not refute it, so the match on `n` still needs a `Succ(m)` branch. That branch is to produce `Eq(Nat(), Succ(m), Zero())`, which `Refl` cannot build.",
      "In that branch, `p : IsZero(Succ(m))`, while `IsZeroHere()` has type `IsZero(Zero())`. So a match on `p` there refutes `IsZeroHere` and has no branches, and, as on the previous page, a match with no branches is allowed any annotation.",
      "Task: add the `Succ` branch, a match on `p` with no branches."),
    boxes: [box(nat, eq, isZero)],
    initial: `-- Add the Succ branch: a match on p there, with no branches.
${isZeroEq("")}`,
    requireQed: false,
    solution: isZeroEq(`
    Succ(m) => match p : _ {};`),
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
      "Here `n` is `times(ten, ten)`, the result of a call, so the checker knows it only by its type, `Nat()` (§7), while the run knows its value: `print n;` shows one hundred `Succ`s around `Zero()`. So it seems no proof of `Even(n)` can be written out: the checker cannot tell whether `n` is `Zero()` or a `Succ`, and neither `EvenZero()` nor an `EvenSucc` checks against the goal. Even where the checker does know the number, as for one written with twenty `Succ`s, a proof written out is twenty nested value constructors, while the reflection below stays one line.",
      "`decideEven(n)`, above, returns `Some` of a proof of `Even(n)` when `n` is even, and `None` otherwise. A plain pattern `let` on its result is rejected: the result too is known only by its type, so forcing does not refute `None` (§10). `comptime let Some(_, p) = e;` evaluates `e` during checking and requires its value to be headed by `Some`; the run, not forcing, rules out `None`, and `p` has type `Even(n)` (§11). It is written only at the top level.",
      "Task: make the `let` a `comptime` pattern `let`, so that `qed p;` proves the goal. Then try `decideEven(Succ(Zero()))` in its place and read the error, which shows the value (§11)."),
    boxes: [box(nat, evenOdd, option, decideEven), hundred],
    initial: `-- Write comptime before this let, so that qed p; proves the goal.
let Some(_, p) = decideEven(n);
qed p;
`,
    requireQed: true,
    solution: `comptime let Some(_, p) = decideEven(n);
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
  {
    slug: "erased",
    title: "Erasure",
    phase: 2,
    prose: paragraphs(
      "From this page on, programs are checked under phase 2, which adds erasure (§16). `vhead` returns the head of a vector; the type `A` and the length `n` are there so that the checker accepts `vhead` only on a vector that is not empty, but evaluating `vhead` never looks at them. A binder marked `erased` says so, and evaluation skips erased positions. Value constructors themselves are never erased, and every value built by one carries its tag, so a vector still says whether it is `VNil` or `VCons`; `print` shows an erased field as `_` (§16).",
      "Every binder has a multiplicity, `many` or `erased`: function parameters and returns, value-constructor fields, the binders of every kind of `let`, and match annotation entries. A binder is `many` unless written `erased` (§16). The multiplicity is written immediately before the binder's name, after any `subterm`, as in `erased n : Nat()` (§16). An erased name is allowed only in an erased position, such as a type or an argument for an erased parameter or field; the next page says more. Type-constructor arguments are always erased, so `Vec(A, Succ(n))` is allowed to mention an erased `A`.",
      "Here `vcons` and `vsecond` take `A` and `n` erased, and the program is rejected at the first place they are passed on to a binder that is `many`. Read the error. Once the program checks, put the caret inside `vsecond`: Scope tags `A` and `n` erased (§13), and in this implementation Expected tags an erased entry the same way (ASSUMPTIONS.md 53).",
      "Task: without changing `vcons` or `vsecond`, mark binders `erased` so that the program checks: `VCons`'s fields `A` and `n`, and `vhead`'s parameters `A` and `n`. `VNil`'s `A` is not used by evaluation either; nothing here requires it, but it is natural to erase it too. Then read what `print v;` shows."),
    boxes: [nat],
    initial: `-- Mark VCons's fields A and n and vhead's parameters A and n erased.
-- Do not change vcons or vsecond.
${vec}
${vheadBy("")}
${erasedUses}`,
    requireQed: false,
    solution: `${vecErased}
${vheadErased}
${erasedUses}`,
  },
  {
    slug: "erased-positions",
    title: "Where erased names go",
    phase: 2,
    prose: paragraphs(
      "§16 allows an erased name only in an erased position: a type, an argument for an erased parameter or field, the result for an erased return or binder, and everything inside these. Anywhere else it is an error. In this implementation the same holds for any erased result, such as a call's result for an erased return (ASSUMPTIONS.md 45).",
      "`len` says that its result `m` is `n` (§6), and returns `n`. But `n` is erased, and the result for the `many` return `m` is not an erased position, so the checker rejects the body at `n`: evaluation skips the argument for `n`, so when `len` runs there is no value of `n` to return.",
      "There are two ways out. Mark the return `erased m is n`: `len`'s result is then erased, and the `let erased k` that binds it is an erased position, which evaluation skips. Or stop erasing the parameter `n`, so that every call passes it. Either way, Scope on the last line shows that `k` is `Succ(Zero())`, so the binder `w : Vec(Nat(), k)` checks, and tags `k` erased, which in this implementation follows from its binder `let erased k` (ASSUMPTIONS.md 53).",
      "Task: make the program check, either way, then try the other. Then add `print len(Nat(), Succ(Zero()), v);`: in this implementation the expression of a `print` is not an erased position (ASSUMPTIONS.md 47), so after the first fix it is rejected, and after the second it shows `Succ(Zero())`."),
    boxes: [box(nat, vecErased)],
    initial: `-- Make this check: erase the return, or stop erasing n.
${len("m is n")}`,
    requireQed: false,
    solution: len("erased m is n"),
  },
  {
    slug: "holes",
    title: "_ for erased arguments",
    phase: 2,
    prose: paragraphs(
      "In phase 2, `_` also stands for an erased argument, solved by unification (§16). In `vhead(_, _, VCons(_, _, Zero(), VNil(_)))`, the head `Zero()` fixes the inner `A` as `Nat()`, the type of `VNil(_)` fixes the inner `n` as `Zero()`, and the vector's type then fixes `vhead`'s `A` and `n`. In this implementation a `_` is also solved from what its position is given (§8; ASSUMPTIONS.md 51): in `let (e : Vec(Nat(), Zero())) = VNil(_);`, the binder's type fixes `VNil`'s `A`.",
      "In this implementation, `_` is allowed only as a whole argument of a call or application in an expression, for an erased parameter or field or a type constructor's argument; not inside a type written in a binder, such as `Vec(_, n)` (ASSUMPTIONS.md 11 and 51). Globals shows which parameters and fields are erased. Put the caret on a `_`: Expected shows the parameter it stands for, tagged erased (ASSUMPTIONS.md 53). Click a `_` to see its solution, canonicalized.",
      "When nothing determines a `_`, as in `print VNil(_);`, the program is rejected. This implementation has a further limit (ASSUMPTIONS.md 51): a `_`'s solution must mention only entries created before the `_`, so a `_` that only a later argument's call result determines is rejected. A block used as an argument takes part in solving through its final expression, as a direct argument does: `vhead(_, _, { v })` checks as `vhead(_, _, v)` does.",
      "Task: replace each erased argument with `_`, and check that the status line still reports the goal proved."),
    boxes: [box(nat, vecErased, vheadErased), "goal Vec(Nat(), Succ(Succ(Zero())));"],
    initial: `-- Replace every erased argument with _; keep the goal proved.
let one = Succ(Zero());
let (e : Vec(Nat(), Zero())) = VNil(Nat());
let v = VCons(Nat(), one, Zero(), VCons(Nat(), Zero(), one, e));
print vhead(Nat(), one, v);
qed VCons(Nat(), one, one, VCons(Nat(), Zero(), Zero(), VNil(Nat())));
`,
    requireQed: true,
    solution: `let one = Succ(Zero());
let (e : Vec(Nat(), Zero())) = VNil(_);
let v = VCons(_, _, Zero(), VCons(_, _, one, e));
print vhead(_, _, v);
qed VCons(_, _, one, VCons(_, _, Zero(), VNil(_)));
`,
  },
  {
    slug: "match-erased",
    title: "Erased matches",
    phase: 2,
    prose: paragraphs(
      "`match erased e : (...)` takes its scrutinee erased; a match written without a multiplicity is `many`. In an erased match, every field of a branch is bound erased (§16). In this implementation the scrutinee of a `many` match is not an erased position (ASSUMPTIONS.md 47), so `match p` on an erased `p` is rejected at `p`.",
      "An erased match with a `many` annotation entry has at most one branch that is not absurd, a branch being absurd when its body is a match with no branches (§16). Evaluation skips the erased scrutinee, so it has no tag to choose a branch by; with only one branch that is not absurd there seems to be nothing to choose. SOUNDNESS.md part 9, which argues erasure only in outline, relies on this. So `match erased n : (r : Nat()) { Zero() => Zero(); Succ(k) => k; }` is rejected at its second branch, while with `erased r` it is allowed. In this implementation the rule applies even to a match that never runs (ASSUMPTIONS.md 48).",
      "`cast` turns a vector of length `m` into one of length `n`, given a proof `p` that `m` and `n` are equal, which matters only to the checker and so is erased. An erased match on `p` forces `Refl`, which equates `m` and `n` (§7), so in its one branch `v` has the type Expected asks for, and evaluation simply returns `v`. The goal is a function goal, as on the \"Proof by recursion\" page; in phase 2 multiplicities must agree too (§12), so `cast`'s binders are erased exactly where the goal's are.",
      "Task: replace `sorry(_)` with an erased match on `p`. Put the caret in its branch: Scope shows that forcing `Refl` added the rule that `n` is `m`. Then the `print` shows the vector, and the goal is proved."),
    boxes: [box(nat, vecErased, eqErased), `goal fn (erased m : Nat(), erased n : Nat(),
    erased p : Eq(Nat(), m, n), v : Vec(Nat(), m))
    -> (w : Vec(Nat(), n));`],
    initial: `-- Replace sorry(_) with an erased match on p.
${castHead}
  sorry(_)
}
${castUse}`,
    requireQed: true,
    solution: `${castHead}
  match erased p : _ {
    Refl(_, _) => v;
  }
}
${castUse}`,
  },
  {
    slug: "tuple-let-telescope",
    title: "Fine points: a let's binders as a telescope",
    phase: 1,
    prose: paragraphs(
      "The pages from here on are a closing section, Fine points. Each shows one rule that was settled while the implementation was being built: all but one are now in DESIGN.md, where the owner confirmed their wording, and one is a choice a Claude session made where DESIGN.md is silent, recorded in ASSUMPTIONS.md. Each page names where its rule is stated.",
      "The binders of a tuple `let` are a telescope (§6): a binder's type or `is` clause is allowed to refer to the binders before it. In `let (m : Nat(), v : Vec(Nat(), Succ(m))) = pair(x);`, `v`'s type mentions `m`. The `let` gives its right-hand side its binders, so `v`'s type is checked with `m` standing for the call's first result, as a function's returns are checked with the earlier returns standing for its results (§8). This seems to be what lets a `let` state the type of every result it binds when one result's type depends on another, as `exchange` on the distributivity page does.",
      "Put the caret on the right-hand side, `pair(x)`: Expected lists both binders, the second mentioning the first (§13). On the `print` line, Scope shows `v : Vec(Nat(), Succ(m))`.",
      "Task: delete `: Nat()` from `m`'s binder and read the error. §6 does not allow a type or `is` clause to refer to a binder that carries neither; in this implementation the error is at the reference, the `m` in `v`'s type, saying that `m` has no type there. Then put the type back so that the program checks again."),
    boxes: [box(nat, vec, pair)],
    initial: `-- Delete m's type, read the error, then restore the type.
let x = Succ(Zero());
let (m : Nat(), v : Vec(Nat(), Succ(m))) = pair(x);
print v;
`,
    requireQed: false,
    solution: `let x = Succ(Zero());
let (m : Nat(), v : Vec(Nat(), Succ(m))) = pair(x);
print v;
`,
  },
  {
    slug: "facts-escape",
    title: "Fine points: facts outlive names",
    phase: 1,
    prose: paragraphs(
      "A pattern `let`'s names are in scope for the rest of the enclosing block, but its fields and facts last to the end of the enclosing match branch or function body, or of the program (§7, §10). So what forcing learned inside a block is still known after it, though the names the pattern gave are gone.",
      "One reason for the rule seems to be that a block's results are allowed to be its pattern's fields: here `h` names the very entry the field `hd` was opened to (§8), and after the block the checker still knows how that entry relates to `v`. A match branch is different: its facts depend on which value constructor the branch is for, so they cannot outlast it.",
      "Look at the `inspect;` after the block, or put the caret on its line. Scope shows `v`'s rule, `VCons(Nat(), n, h, ...)`, still in force. The field `hd` appears as `h`, the name the tuple `let` gave its entry, and the tail, which the pattern named `tl`, appears as an anonymous entry, marked as `VCons`'s field `rest` and where it was created (§13): the entry is there, the name is not.",
      "Task: the goal is that `v` is the `VCons` of `h` and a tail `t`. Bind `t` with a second pattern `let` on `v` before the goal, then prove it with `qed`. It checks only because the block's fact escaped: forcing the second pattern `let` equates `v`'s known `VCons` with the new one, so its head is `h`."),
    boxes: [box(nat, vec, eq, pair), escaped],
    initial: `-- Bind v's tail as t before the goal, then prove the goal.
${escapedGoal}
`,
    requireQed: true,
    solution: `let VCons(_, _, _, t) = v;
${escapedGoal}
qed Refl(Vec(Nat(), Succ(n)), v);
`,
  },
  {
    slug: "poison",
    title: "Fine points: a poisoned body",
    phase: 1,
    prose: paragraphs(
      "Your box has the previous page's shape, but `v` comes from `sorry`. Forcing `VCons` on it adds facts that nothing backs, and they last as long as any pattern `let`'s facts: to the end of the enclosing match branch or function body, or of the program (§7). So the taint reaches as far: a pattern `let` whose scrutinee is tainted taints every result of the match branch or function body it is in, or, at the top level, every result of the top-level statements after it (§12). After it, at the top level, nothing evaluates, every `print` shows `sorry` and no `qed` proves the goal, though checking goes on.",
      "The reason is soundness: a fact forced from a `sorry` can make later code check that otherwise would not, such as an `is` clause or a `qed`, so everything those facts reach is treated as relying on the `sorry`. Every statement in your box checks, yet the status line reports that the goal is not proved, and `print n;` shows `sorry`, although `n` has nothing to do with `v` and the box above printed it.",
      "The box above has the same pattern `let` inside a match branch. There its facts end with the branch, and it taints only the match's results: `print c;` shows `sorry`, while `print n;` after it shows `Zero()` (§12).",
      "Task: replace the `sorry` with a real vector of type `Vec(Nat(), Succ(Zero()))`, so that the goal is proved. The status line still reports `sorry` in the program, from the box above."),
    boxes: [box(nat, vec, eq, pair), inBranch],
    initial: `-- Replace the sorry with a real vector, so that the goal is proved.
-- Keep the pattern let on v.
${poisonedLet("sorry(v : Vec(Nat(), Succ(Zero())))")}`,
    requireQed: true,
    solution: poisonedLet("VCons(Nat(), Zero(), Zero(), VNil(Nat()))"),
  },
  {
    slug: "hole-through-block",
    title: "Fine points: _ through a block",
    phase: 2,
    prose: paragraphs(
      "In this implementation, a block used as an argument takes part in solving the call's `_`s through its final expression, as a direct argument does; the block's statements do not, nor does a match branch's body. This is ASSUMPTIONS.md 51, a choice a Claude session made where DESIGN.md is silent, not a decision by the owner.",
      "§8 says a block gives its final expression what the block is given, so treating the final expression as the argument seems the reading closest to it; otherwise wrapping an argument in a block could leave a `_` that nothing solves. So `vhead(_, _, { v })` checks as `vhead(_, _, v)` does: `v`'s type, `Vec(Nat(), Succ(Zero()))`, is unified with the parameter's, `Vec(A, Succ(n))`.",
      "Once your box uses `_`, put the caret on each `_`: Expected shows the parameter it stands for, tagged erased (ASSUMPTIONS.md 53). Click a `_`, or press \"Explain the term at the caret\", to see its solution: `Nat()` for `A` and `Zero()` for `n`.",
      "Task: replace `vhead`'s erased arguments with `_` in both calls, and check that both still print."),
    boxes: [box(nat, vecErased, vheadErased), `let one = Succ(Zero());
let v = VCons(_, _, one, VNil(_));`],
    initial: `-- Replace vhead's erased arguments with _ in both calls.
${throughBlock("Nat()", "Zero()")}`,
    requireQed: false,
    solution: throughBlock("_", "_"),
  },
  {
    slug: "hole-taint",
    title: "Fine points: _ and taint",
    phase: 2,
    prose: paragraphs(
      "A `_` is tainted when the term it is solved to mentions a tainted entry (§12). Here `count`'s parameter has type `Vec(A, Zero())`, and `A` comes from `sorry`, so the `_` in `VNil(_)` is solved to `A` and is tainted, and so is the call, as it would be with `VNil(A)` written out.",
      "The reason is soundness: without the rule, writing `_` where a tainted argument belongs would hide the taint, and a call relying on a `sorry` could prove a goal.",
      "Click either `_`: its solution is `A`. The status line reports that the `qed` checks and the goal is not proved, and the `print` shows `sorry`.",
      "Task: replace `sorry(A : Type())` with `Nat()`. The `_` is then solved to an untainted entry, the `print` shows `Zero()`, and the goal is proved."),
    boxes: [box(nat, vecErased), "goal Nat();"],
    initial: `-- Replace sorry(A : Type()) with Nat(), so that the goal is proved.
-- Change nothing else.
${taintedHole("sorry(A : Type())")}`,
    requireQed: true,
    solution: taintedHole("Nat()"),
  },
  {
    slug: "goal-comparison",
    title: "Fine points: comparing a function with a goal",
    phase: 1,
    prose: paragraphs(
      "`qed f;` checks `f`'s parameters and returns against a function goal's, position by position (§12). They are compared as terms whose bound variables refer to their binders, so binder names play no part, and an earlier binder's `is` clause is not in force for later ones; `is` clauses, and in phase 2 multiplicities, must agree; `subterm` marks are not compared.",
      "So the comparison is between the two signatures as written. A `subterm` mark seems to say how `f` recurses (§9), which the goal does not state, so leaving marks out lets a recursive function prove a goal written without them.",
      "`succEq` names its binders `x` and `y` and marks `x` `subterm`, which the goal does not; neither matters. But its return is `Eq(Nat(), Succ(x), y)`, and the goal's is `Eq(Nat(), b, Succ(a))`. With `y is Succ(x)` in force the two would canonicalize alike, but the comparison does not use it, so the program is rejected at `succEq` in the `qed`, and the error names return 1, with the binders named as in the goal. Put the caret on that name: Expected shows the goal's parameters and returns.",
      "Task: make the `qed` prove the goal, by changing either the goal or `succEq`'s return."),
    boxes: [box(nat, eq)],
    initial: `-- Change the goal or succEq so that the qed proves the goal.
${succEq("Succ(x), y")}`,
    requireQed: true,
    solution: succEq("y, Succ(x)"),
  },
  {
    slug: "absurd-branches",
    title: "Fine points: absurd branches",
    phase: 2,
    prose: paragraphs(
      "An erased match with a `many` annotation entry is allowed at most one branch that is not absurd; a branch is absurd when its body is a match with no branches, possibly the final expression of a block. Evaluation runs the branch that is not absurd (§16).",
      "An erased match has no value of its scrutinee to choose a branch by, which is why it is allowed only one branch that can run. An absurd branch seems never to run: its match has no branches because every value constructor of its scrutinee's type is refuted there. Allowing it is what lets an erased match use a proof to rule out a value constructor, as on the page \"Refuting through a proof\", where §10 requires the branch. Here `f` takes `n` erased, since its result never needs it.",
      "Once your box checks, put the caret on `match erased`: Refutations lists `Succ` as absurd (§13). Put it on the inner `match p`: Refutations lists `IsZeroHere` as refuted, and opening it shows why. The `print` shows `Zero()`, from the branch that is not absurd.",
      "Task: write the `Succ` branch as an absurd one: match on `p` there, with no branches."),
    boxes: [box(nat, isZero)],
    initial: `-- Add the Succ branch: an absurd one, matching on p.
${absurdHead}
${absurdUse}`,
    requireQed: false,
    solution: `${absurdHead}
    Succ(m) => match p : _ {};
${absurdUse}`,
  },
];
