import type { Section } from "./pages.ts";
import { nat } from "../examples.ts";
import { paragraphs, box, evenOdd, plusFn, eq, isZero, plusRel, plus } from "./programs.ts";

const falseType = `data False() : Type() {}`;

const isZeroEq = (succBranch: string): string => `fn f(n : Nat(), p : IsZero(n)) -> (e : Eq(Nat(), n, Zero())) {
  match n : _ {
    Zero() => Refl(Nat(), n);${succBranch}
  }
}
`;

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

export const proofs: Section = { title: "Proofs", pages: [
  {
    slug: "equality",
    title: "Propositions as types: equality",
    phase: 1,
    prose: paragraphs(
      "A type can be read as a proposition and a value of it as a proof. The data type constructor `Eq` below has one value constructor, `Refl(A, x) : Eq(A, x, x)`, so, `sorry` (a later page) aside, a value of `Eq(A, x, y)` is built only by `Refl`, whose type has the same `x` on both sides.",
      "`goal T;` sets the program's goal and `qed e;` checks `e` against it (§12). The status line reports whether the `qed` checks and whether the goal is proved. On this page the `qed` must be in your box."),
    task: "Prove the goal. Since `two` canonicalizes to `Succ(Succ(Zero()))`, one `Refl` should do.",
    refs: "§12",
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
    slug: "empty",
    title: "Empty types and False()",
    phase: 1,
    prose: paragraphs(
      "`False` here is a data type constructor that declares no value constructors, unrelated to the value constructor `False` of `Bool` on earlier pages. A match on a value of `False()` has no branches, so its annotation can be any telescope, as `absurd` shows (§10).",
      "A function returning `False()` can be read as a proof that its parameters' types cannot all have values. SOUNDNESS.md, an argument that is not machine-checked, argues that in an accepted program without `sorry`, no `qed` proves `False()`: the `qed`'s expression would evaluate to a value of `False()`, which only a value constructor of `False` could build, and there is none."),
    task: "Show that `Zero()` and `Succ(Zero())` are not equal. The branch for `Refl` is an error, because `Refl` is refuted; open it under Refutations to see why.",
    refs: "§10",
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
      "In that branch, `p : IsZero(Succ(m))`, while `IsZeroHere()` has type `IsZero(Zero())`. So a match on `p` there refutes `IsZeroHere` and has no branches, and, as on the previous page, a match with no branches is allowed any annotation."),
    task: "Add the `Succ` branch, a match on `p` with no branches.",
    refs: "§10",
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
      "Taint tracks what relies on a `sorry`: roughly, its results and what is built from them; §12 gives the rules. An expression whose results are all tainted is removed before evaluation, so `print p;` shows `sorry`, and a `qed` of a tainted result checks without proving the goal. Look at the status line: it says the program contains `sorry`, the `qed` checks, and the goal is not proved."),
    task: "Replace the `sorry` with real evidence that four is even.",
    refs: "§12",
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
    slug: "plus-zero",
    title: "Proof by recursion",
    phase: 1,
    prose: paragraphs(
      "Types never contain function calls (§3), so `Eq(Nat(), plus(n, Zero()), n)` cannot be written. Here `plus` instead returns, beside its result `r`, a value of the data type `Plus(m, n, r)`, read as a proof that `m` plus `n` is `r`.",
      "The goal on this page is a function goal (§12): the parameters and returns of a function, with no name and no body, read as: for every `n` and `r`, a proof of `Plus(n, Zero(), r)` gives a proof of `Eq(Nat(), r, n)`. `qed plusZero;` names a function, and checks when `plusZero`'s parameters and returns are canonically identical to the goal's, position by position, binder names aside; `subterm` marks are not compared, so `plusZero` is allowed to mark `n` `subterm` (§12). Nothing is passed or returned, so functions are still not first class (§4).",
      "`plusZero`, by recursion on `n`, turns a proof of `Plus(n, Zero(), r)` into one of `Eq(Nat(), r, n)`. Matching on a value of `Eq` forces `Refl`, which equates the two sides of the `Eq` (§7): in that branch they canonicalize to the same term."),
    task: "Add the `PlusSucc` branch. In it, `n` canonicalizes to `Succ(m)` for the branch's first field `m`: call `plusZero(subterm m, ...)` on the inner proof and match on the `Eq` it returns. Then prove the goal with `qed plusZero;`.",
    refs: "§3, §4, §7, §12",
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
      "The read-only box below also shows `plusZeroRight`, which builds a proof that `n` plus zero is `n` by recursion on `n`. It is the previous page's fact in another form, producing the `Plus` proof rather than taking one apart. This page does not use it; the next one does."),
    task: "Write the two branches, then prove the goal with `qed plusSucc;`. Put the caret on each branch body: Scope shows what forcing the value constructor added, such as `m` being `Zero()` in the `PlusZero` branch, and Expected shows the type the branch is to produce. In the `PlusSucc(m1, _, r1, p1)` branch, a recursive call `plusSucc(m1, n, r1, subterm p1)` gives `Plus(m1, Succ(n), Succ(r1))`.",
    refs: "§9, §12",
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
      "The goal is commutativity: if `m` plus `n` is `r`, then `n` plus `m` is `r`. The proof is again an induction on `m`, as a recursion on `p`, and each branch needs one of the two lemmas below.",
      "In the `PlusZero` branch, `m` is `Zero()` and `r` is `n`, so the branch is to produce `Plus(n, Zero(), n)`. `Plus`'s value constructors follow its first argument, not its second, so none of them builds this directly for an unknown `n`; `plusZeroRight(n)` does, by its own induction on `n`.",
      "In the `PlusSucc(m1, _, r1, p1)` branch, `m` is `Succ(m1)`, `r` is `Succ(r1)` and `p1 : Plus(m1, n, r1)`. The recursive call `plusComm(m1, n, r1, subterm p1)` gives `Plus(n, m1, r1)`, and the branch is to produce `Plus(n, Succ(m1), Succ(r1))`: that is what `plusSucc` from the previous page gives, applied to `n`, `m1` and `r1`."),
    task: "Write both branches, checking each against the Expected and Scope panels, and prove the goal with `qed plusComm;`.",
    refs: "§9, §12",
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
      "The recursive call marks `p1` `subterm`. With the caret in the body, Termination lists `p` as `plusAssoc`'s `subterm` parameter, and Scope shows that `p` canonicalizes to `PlusSucc(a1, b, ab1, p1)`, so `p1` is a strict subterm of it (§9). The call gives `bc`, `s1 : Plus(b, c, bc)` and `s2 : Plus(a1, bc, r1)`, and `PlusSucc` turns `s2` into the `Plus(Succ(a1), bc, Succ(r1))` that Expected asks for."),
    task: "Write the `PlusZero` branch where the comment is. There `a` is `Zero()` and `ab` is `b`, so `q : Plus(b, c, r)`; Expected shows what is left to choose. The `qed` is already in your box.",
    refs: "§9, §10",
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
      "`exchange` below, (w + y) + (x + z) = (w + x) + (y + z), has no recursion of its own: it chains associativity, read in both directions (`plusAssoc`, and `plusAssocRev`, proved by recursion on its second proof), and commutativity. Each `let` in it gives the type of every value it binds, and such a type can mention the binders before it in the same `let`, such as `yxz`; the checker checks each against the result the binder names. A binder referred to this way needs a type of its own, which is why `yxz` carries `: Nat()`: without one, the reference is an error. Put the caret on each line and compare Scope with these types."),
    task: "Write the `TimesZero` branch where the comment is. There `a` and `r` are `Zero()`; Expected shows what is to be produced.",
    refs: "§6, §9, §12",
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
    slug: "comptime",
    title: "Proof by reflection",
    phase: 1,
    prose: paragraphs(
      "Here `n` is `times(ten, ten)`, the result of a call, so the checker knows it only by its type, `Nat()` (§7), while the run knows its value: `print n;` shows one hundred `Succ`s around `Zero()`. So it seems no proof of `Even(n)` can be written out: the checker cannot tell whether `n` is `Zero()` or a `Succ`, and neither `EvenZero()` nor an `EvenSucc` checks against the goal. Even where the checker does know the number, as for one written with twenty `Succ`s, a proof written out is twenty nested value constructors, while the reflection below stays one line.",
      "`decideEven(n)`, below, returns `Some` of a proof of `Even(n)` when `n` is even, and `None` otherwise. A plain pattern `let` on its result is rejected: the result too is known only by its type, so forcing does not refute `None` (§10). `comptime let Some(_, p) = e;` evaluates `e` during checking and requires its value to be headed by `Some`; the run, not forcing, rules out `None`, and `p` has type `Even(n)` (§11). It is written only at the top level."),
    task: "Make the `let` a `comptime` pattern `let`, so that `qed p;` proves the goal. Then try `decideEven(Succ(Zero()))` in its place and read the error, which shows the value (§11).",
    refs: "§7, §10, §11",
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
      "`loop` in your box tries to prove `False()` by calling itself, and is rejected by the termination rule (§9). Try other ways if you like: passing a function as an argument, or writing a call in a type."),
    task: "Make the program check. The only way this tutorial knows is `sorry`, and then the status line reports that the program contains `sorry` and that the goal is not proved.",
    refs: "§3, §9",
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
] };
