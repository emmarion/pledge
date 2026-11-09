import type { Section } from "./pages.ts";
import { nat, vec, vheadBy } from "../examples.ts";
import { paragraphs, box, evenOdd, plusFn, eq, isZero, plusRel, plus } from "./programs.ts";

const gap = " sorry(_)";

const withQed = (fn: string, name: string): string => `${fn}
qed ${name};
`;

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

const plusZero = (zero: string, succ: string): string =>
  `fn plusZero(subterm n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
    -> (e : Eq(Nat(), r, n)) {
  match p : _ {
    PlusZero(_) =>${zero};
    PlusSucc(m, _, r1, q) =>${succ};
  }
}`;

const plusZeroRight = `fn plusZeroRight(subterm n : Nat()) -> (p : Plus(n, Zero(), n)) {
  match n : _ {
    Zero() => PlusZero(Zero());
    Succ(k) => PlusSucc(k, Zero(), k, plusZeroRight(subterm k));
  }
}`;

const vappend = (nil: string, cons: string): string =>
  `fn vappend(A : Type(), m : Nat(), n : Nat(), subterm v : Vec(A, m),
    w : Vec(A, n)) -> (r : Nat(), p : Plus(m, n, r), u : Vec(A, r)) {
  match v : _ {
    VNil(_) =>${nil};
    VCons(_, m1, x, rest) =>${cons};
  }
}
qed vappend;
let (r, p, u) = vappend(Nat(), two, one, xs, ys);
print r;
print u;
`;

const lemma = (name: string, conclusion: string) => ({
  fn: (zero: string, succ: string): string => `fn ${name}(m : Nat(), n : Nat(), r : Nat(), subterm p : Plus(m, n, r))
    -> (q : ${conclusion}) {
  match p : _ {
    PlusZero(_) =>${zero};
    PlusSucc(m1, _, r1, p1) =>${succ};
  }
}`,
  goal: `goal fn (m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    -> (q : ${conclusion});`,
});

const plusSuccLemma = lemma("plusSucc", "Plus(m, Succ(n), Succ(r))");

const plusSucc = plusSuccLemma.fn(" PlusZero(Succ(n))", `
      PlusSucc(m1, Succ(n), Succ(r1), plusSucc(m1, n, r1, subterm p1))`);

const plusCommLemma = lemma("plusComm", "Plus(n, m, r)");

const plusComm = plusCommLemma.fn(" plusZeroRight(n)", `
      plusSucc(n, m1, r1, plusComm(m1, n, r1, subterm p1))`);

const plusAssocWith = (zero: string): string => `fn plusAssoc(a : Nat(), b : Nat(), c : Nat(), ab : Nat(), r : Nat(),
    subterm p : Plus(a, b, ab), q : Plus(ab, c, r))
    -> (bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(a, bc, r)) {
  match p : _ {
    PlusZero(_) =>${zero};
    PlusSucc(a1, _, ab1, p1) => {
      let PlusSucc(_, _, r1, q3) = q;
      let (bc, s1, s2) = plusAssoc(a1, b, c, ab1, r1, subterm p1, q3);
      (bc, s1, PlusSucc(a1, bc, r1, s2))
    };
  }
}`;

const plusAssoc = plusAssocWith(" (r, q, PlusZero(r))");

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

const timesDistrib = (zero: string): string => `fn timesDistrib(a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), subterm t : Times(a, bc, r))
    -> (ab : Nat(), ac : Nat(), t1 : Times(a, b, ab),
        t2 : Times(a, c, ac), q : Plus(ab, ac, r)) {
  match t : _ {
    TimesZero(_) =>${zero};
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

const four = `let three = Succ(Succ(Succ(Zero())));
let four = Succ(three);
goal Even(four);`;

const fourIsEven = (proof: string): string => `let p : Even(four) = ${proof};
print p;
qed p;
`;

const replaceAll = "Replace each `sorry(_)` in your box, until the status line reads \"No sorry\" and \"Goal proved\".";

export const proofs: Section = { title: "Proofs", pages: [
  {
    slug: "equality",
    title: "Propositions as types: equality",
    phase: 1,
    prose: paragraphs(
      "So far, types have described data. On the page about `Even` and `Odd`, a type began to say more: a value of `Even(n)` can only be built when `n` is even. This section takes that idea as far as it goes. A type can be read as a claim, and a value of the type as evidence that the claim holds. To show that a claim is true, you write a value of its type, and the checker checks it.",
      "For example, `EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()))` has type `Even(Succ(Succ(Zero())))`, so it is evidence that two is even. No value has type `Even(Succ(Zero()))`: no combination of the value constructors of `Even` and `Odd` builds one. So nothing shows that one is even, as long as you leave out `sorry`, which comes three pages on. This way of reading types is known as propositions as types.",
      "The first box declares a type for equality. `Eq(A, x, y)` is the claim that `x` and `y`, two values of type `A`, are equal. It has one value constructor, `Refl(A, x)`, and its type is `Eq(A, x, x)`, with the same `x` on both sides. So a `Refl` is evidence that two terms are equal when the checker sees the same canonical form on both sides. (`Refl` is short for reflexivity: everything equals itself.)",
      "The second box ends with `goal Eq(Nat(), two, Succ(Succ(Zero())));`. A *goal* states the claim a program sets out to prove: the type it means to give a value of. A *`qed`* statement, `qed e;`, offers `e` as that value, and the checker checks `e` against the goal. A program has at most one of each, at the top level, with the `qed` after the `goal`. On this page you write the `qed`.",
      "`Refl(Nat(), two)` has type `Eq(Nat(), two, two)`. Does that fit the goal? The checker compares canonical forms, and `two` canonicalizes to `Succ(Succ(Zero()))`. Put the caret on `two` in the `goal` line: the Term panel shows the rewrites. If the types do not fit, the error names both.",
      "The status line under your box now reads \"No qed in your box\" and \"Goal not proved\"; once your `qed` checks, \"qed checks\" and \"Goal proved\"."),
    task: "Prove the goal: write `qed` with one `Refl` in your box.",
    refs: "§3, §5, §7, §12, §13",
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
      "Some things you want to prove are negative: zero is not one, an empty list has no first element. To say \"this cannot happen\" with a type, you need a type that has no values.",
      "The first box declares one: `False()`, with no value constructors at all, so no value of it can be built. A type like this is called an empty type. (This `False` is a type constructor, and has nothing to do with the value constructor `False` of `Bool` in the Basics section.)",
      "A function that returns `False()` can be read as evidence that its parameters cannot all have values: if they had, the function would produce a value of `False()`, and there is none. `zeroNotOne` in your box takes evidence that `Zero()` equals `Succ(Zero())` and returns `False()`. So it shows that zero is not one.",
      "How can its body produce a `False()`? It does not have to. The `match` on `e` needs a branch for each value constructor of `Eq` that is not refuted, and `Refl` is refuted: if `e` were a `Refl`, `Zero()` and `Succ(Zero())` would have to be the same value. So the match has no branches. With no branch to check, it can promise any telescope after the colon. That is how `absurd`, in the second box, turns a `False()` into a `Nat()`, and so into anything else.",
      "This is why it matters that no accepted program builds a value of `False()`: with one, `absurd` and its like would prove every claim. SOUNDNESS.md, a written argument that is not machine-checked, argues that in an accepted program without `sorry`, no `qed` proves `False()`: the `qed`'s expression would evaluate to a value of `False()`, which only a value constructor of `False` could build, and there is none."),
    task: "Your branch for `Refl` is an error, because `Refl` is refuted. Put the caret on `match` and open `Refl` under Refutations: it lists the steps by which `Refl`'s `x` would have to be both `Zero()` and `Succ(Zero())`. Then delete the branch.",
    refs: "§5, §7, §10, §13",
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
      "Evidence is also useful as input. `f` in your box takes a number `n` and evidence `p : IsZero(n)`, and returns evidence that `n` equals `Zero()`. `IsZero`, in the first box, has one value constructor, `IsZeroHere()`, of type `IsZero(Zero())`, so a value of `IsZero(n)` can only be built when `n` is zero.",
      "You might expect the match on `n` to need no branch for `Succ`, since `p` rules it out. It does need one, and the error says so. The checker refutes a value constructor only by what it knows about the scrutinee, `n`, and its type. `p` is neither, so it does not refute anything by itself. One reason for the rule seems to be that it keeps refutation easy to follow: the checker never searches the scope for evidence, and you choose which evidence to take apart.",
      "So write the `Succ(m)` branch. It is to produce `Eq(Nat(), Succ(m), Zero())`, which `Refl` cannot build. But forcing `Succ` told the checker that `n` is `Succ(m)`, so in that branch Scope shows `p : IsZero(Succ(m))`. A match on `p` there refutes `IsZeroHere`, whose type is `IsZero(Zero())`.",
      "That match has no branches, so, like the match in `zeroNotOne` on the previous page, it can produce whatever its annotation says. Write `_` as the annotation: it stands for what the branch is to produce."),
    task: "Add the `Succ(m)` branch: a match on `p` with no branches. Then put the caret on that `match` and open `IsZeroHere` under Refutations.",
    refs: "§7, §10, §13",
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
      "The proofs from here on are longer, and you will not write them in one go. You need a way to leave a gap, have the rest checked anyway, and see what belongs in the gap.",
      "*`sorry`* is that gap. `sorry(q : Odd(three))` is a value of type `Odd(three)` with nothing behind it. Inside the parentheses is a telescope, as after a function's arrow, so one `sorry` can stand for several values. Checking goes on past it as past any other expression.",
      "Usually you need not write the telescope. `sorry(_)` takes it from where it stands, at a place that says what must be produced: a function body, a branch body, or a `let` whose binders all have types, like `let p : Even(four)` in your box. Put the caret on `sorry(_)`: Expected shows `p : Even(Succ(Succ(Succ(Succ(Zero())))))`, the gap's type, and Scope shows what you can use to fill it. An argument is not such a place, so there you write the telescope out.",
      "A `sorry` proves nothing, so nothing built from it should count. The checker records what relies on a `sorry`, and calls this *taint*. Here `p` is tainted: put the caret on the `print` line, and Scope marks it. A tainted result is not evaluated, so `print p;` shows `sorry`. The `qed` still checks, since the types fit, but the goal is not proved. The status line says so: \"Contains sorry\", \"qed checks\", \"Goal not proved\".",
      "This is how to work on the pages that follow. Each starts with `sorry(_)` in every gap you are to fill. Put the caret on a gap, read Expected and Scope, and replace it. You are done when the status line reads \"No sorry\" and \"Goal proved\"."),
    task: "Replace `sorry(_)` with real evidence that four is even. You can go one layer at a time: first write `EvenSucc(three, sorry(q : Odd(three)))`, then put the caret on the new `sorry` to see what is left.",
    refs: "§8, §10, §12, §13",
    boxes: [box(nat, evenOdd), four],
    initial: `-- Replace sorry(_) with evidence that four is even.
${fourIsEven("sorry(_)")}`,
    requireQed: true,
    solution: fourIsEven(`EvenSucc(three,
  OddSucc(Succ(Succ(Zero())),
    EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()))))`),
  },
  {
    slug: "plus-zero",
    title: "Proof by recursion",
    phase: 1,
    prose: paragraphs(
      "Now a claim about every number at once: adding zero to a number gives the number back. You cannot check that by trying numbers; it takes a proof.",
      "In many languages with proofs, you would state it as `Eq(Nat(), plus(n, Zero()), n)`. In Pledge you cannot: a type contains no function call, and writing one there is an error. The last page of this section comes back to why.",
      "Pledge describes addition by a type instead. `Plus(m, n, r)` is the claim that `m` plus `n` is `r`. Its value constructors are the two cases of addition: `PlusZero(n)` is evidence that zero plus `n` is `n`, and `PlusSucc(m, n, r, p)` turns evidence `p` that `m` plus `n` is `r` into evidence that `Succ(m)` plus `n` is `Succ(r)`. The `plus` in the first box returns its result `r` together with evidence `p : Plus(m, n, r)`. This way of stating things has costs, which the last page of the main path, \"What Pledge leaves out\", returns to.",
      "The claim is now: for every `n` and `r`, if `n` plus zero is `r`, then `r` equals `n`. The second box states it as a *function goal*: a function's parameters and returns, with no name and no body. This tutorial reads it as \"for all such parameters there are such returns\". A function with the same parameters and returns proves it, and `qed plusZero;` names that function; on this page you write the `qed` yourself. The checker compares the two position by position; binder names and `subterm` marks need not agree. `qed` only names the function: it does not pass it anywhere.",
      "`plusZero` is a recursion on `n`, marked `subterm`, that takes apart the evidence `p`. A function that handles zero directly, and `Succ(m)` by calling itself on `m`, covers every number. Read as a proof, that is a proof by induction.",
      "Put the caret on the first `sorry(_)`. Scope shows that forcing `PlusZero` told the checker that `n` and `r` are both `Zero()`, and Expected asks for `e : Eq(Nat(), Zero(), Zero())`. One `Refl` does it.",
      "On the second `sorry(_)`, Scope shows that `n` is `Succ(m)`, `r` is `Succ(r1)` and `q : Plus(m, Zero(), r1)`, and Expected asks for `Eq(Nat(), Succ(r1), Succ(m))`. The call `plusZero(subterm m, r1, q)` gives evidence of `Eq(Nat(), r1, m)`. That is almost it, but a `Refl` needs the same term on both sides, and `r1` and `m` are different entries.",
      "So match on the evidence the call returns. Forcing `Refl` equates the two sides of the `Eq`, so in the `Refl` branch the checker knows that `r1` is `m`, and Scope shows it. Expected is then `Eq(Nat(), Succ(m), Succ(m))`, and a `Refl` fits. While a `sorry` is left in `plusZero`, the call relies on it, and Scope reports the `Refl` branch as tainted by that call."),
    task: "Replace both `sorry(_)`, then write `qed plusZero;` below the function, until the status line reads \"No sorry\" and \"Goal proved\".",
    refs: "§3, §7, §9, §10, §12, §13",
    boxes: [box(nat, eq, plus), `goal fn (n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
    -> (e : Eq(Nat(), r, n));`],
    initial: `-- Replace each sorry(_), then prove the goal with qed plusZero;
${plusZero(gap, gap)}
`,
    requireQed: true,
    solution: withQed(plusZero(" Refl(Nat(), r)", ` match plusZero(subterm m, r1, q) : _ {
      Refl(_, _) => Refl(Nat(), r);
    }`), "plusZero"),
  },
  {
    slug: "vappend",
    title: "Appending vectors",
    phase: 1,
    prose: paragraphs(
      "Appending puts one vector after another: lengths m and n give a vector of length m + n. The type of `vappend` should say so, as `vhead`'s type said \"not empty\". In some other languages, as far as this tutorial knows, you would write the result's type as `Vec(A, m + n)`. In Pledge you cannot: as the previous page showed, a type contains no function call.",
      "So `vappend` does what `plus` did on the previous page, and the first box shows `plus` again: it returns the answer together with evidence. Its returns are a length `r`, evidence `p : Plus(m, n, r)`, and the vector `u : Vec(A, r)`. You can read them as \"there is an `r` such that m + n = r and `u` has length `r`\". The second box states this as a function goal, and `qed vappend;` is already in your box.",
      "As `plus` is a recursion on `m`, `vappend` is a recursion on `v`, the first of the two vectors, marked `subterm`. Put the caret on the first `sorry(_)`: Scope shows that `m` is `Zero()` and `v` is `VNil(A)`, and Expected asks for `r : Nat()`, `p : Plus(Zero(), n, r)` and `u : Vec(A, r)`.",
      "On the second, Scope shows that `m` is `Succ(m1)` and `v` is `VCons(A, m1, x, rest)`, so `rest` is a strict subterm of `v`. Write the branch as `plus` writes its `Succ(k)` branch: a block whose tuple `let` binds the three results of `vappend(A, m1, n, subterm rest, w)`, say as `r1`, `p1` and `u1`. With a `sorry(_)` as the block's last expression, Scope there shows `p1 : Plus(m1, n, r1)` and `u1 : Vec(A, r1)`, marked tainted while a `sorry` is left in `vappend`.",
      "Then build the three results: one more on the length, a `PlusSucc` around the evidence, a `VCons` around the vector. Each element of the tuple has its own Expected, with the earlier ones filled in: after `Succ(r1)`, the second asks for `p : Plus(Succ(m1), n, Succ(r1))`.",
      "The run then prints three and the appended vector, but the checker knows less. Put the caret on the last line: Scope shows `r : Nat()` with no rule and `u : Vec(Nat(), r)`. As on the page \"is binders\", the checker knows a call's results only by the function's returns. So the call `vhead(Nat(), two, u)`, which needs a vector of length three, is rejected. This seems to be the price of stating addition as a relation; the last page of the main path, \"What Pledge leaves out\", comes back to it."),
    task: "Replace each `sorry(_)`, until the status line reads \"No sorry\" and \"Goal proved\". Then add `print vhead(Nat(), two, u);` at the end of your box, read the error, and delete the line.",
    refs: "§3, §7, §8, §9, §10, §12, §13",
    boxes: [box(nat, vec, plus, vheadBy("")), `let one = Succ(Zero());
let two = Succ(one);
let xs = VCons(Nat(), one, Zero(),
  VCons(Nat(), Zero(), one, VNil(Nat())));
let ys = VCons(Nat(), Zero(), two, VNil(Nat()));
goal fn (A : Type(), m : Nat(), n : Nat(), v : Vec(A, m), w : Vec(A, n))
    -> (r : Nat(), p : Plus(m, n, r), u : Vec(A, r));`],
    initial: `-- Replace each sorry(_), then read what the two prints show.
${vappend(gap, gap)}`,
    requireQed: true,
    solution: vappend(" (n, PlusZero(n), w)", ` {
      let (r1, p1, u1) = vappend(A, m1, n, subterm rest, w);
      (Succ(r1), PlusSucc(m1, n, r1, p1), VCons(A, r1, x, u1))
    }`),
  },
  {
    slug: "plus-succ",
    title: "A lemma about Plus",
    phase: 1,
    prose: paragraphs(
      "This page and the next three prove facts about arithmetic that you know from school. Writing a + b = c for `Plus(a, b, c)`, this page proves: if m + n = r, then m + (n + 1) = r + 1, where n + 1 is `Succ(n)`. It is a lemma, a small fact proved to help with a bigger one: the next page needs it for commutativity.",
      "Each fact is a function goal, as on the page \"Proof by recursion\": the parameters are the assumptions, and the returns are the conclusion. As on the previous page, `qed plusSucc;` is already in your box, so the status line reads \"qed checks\" and \"Goal not proved\" from the start.",
      "The proof is an induction on m, written as a recursion on the evidence `p`, which is marked `subterm`. The match on `p` has one branch for each way m + n = r can have been shown.",
      "Put the caret on the first `sorry(_)`. Scope shows that `m` is `Zero()` and `r` is `n`, so Expected asks for `Plus(Zero(), Succ(n), Succ(n))`: zero plus `Succ(n)` is `Succ(n)`. One `PlusZero` shows that.",
      "On the second, `m` is `Succ(m1)`, `r` is `Succ(r1)` and `p1 : Plus(m1, n, r1)`, and Expected asks for `Plus(Succ(m1), Succ(n), Succ(Succ(r1)))`. Scope also shows that `p` is `PlusSucc(m1, n, r1, p1)`, so `p1` is a strict subterm of `p`, and the recursive call `plusSucc(m1, n, r1, subterm p1)` is allowed. It gives `Plus(m1, Succ(n), Succ(r1))`, and one `PlusSucc` around it gives what Expected asks for.",
      "The first box also holds `plusZeroRight`, evidence that n + 0 = n, built by recursion on `n`. It is the fact of the page \"Proof by recursion\" in another form: it produces evidence of `Plus` instead of taking it apart. This page does not need it; the next one does."),
    task: replaceAll,
    refs: "§7, §9, §12, §13",
    boxes: [box(nat, plusRel, plusZeroRight), plusSuccLemma.goal],
    initial: `-- Replace each sorry(_).
${withQed(plusSuccLemma.fn(gap, gap), "plusSucc")}`,
    requireQed: true,
    solution: withQed(plusSucc, "plusSucc"),
  },
  {
    slug: "plus-comm",
    title: "Commutativity of addition",
    phase: 1,
    prose: paragraphs(
      "This page proves that the order of a sum does not matter: if m + n = r, then n + m = r. That looks too obvious to need a proof, but `Plus` is defined by cases on its first argument, so its value constructors say nothing directly about the second. Swapping the two takes an induction, and the two lemmas in the second box do the steps.",
      "As on the previous page, the proof is a recursion on `p`, and the `qed` is already in your box.",
      "Put the caret on the first `sorry(_)`. Scope shows that `m` is `Zero()` and `r` is `n`, so Expected asks for `Plus(n, Zero(), n)`: n + 0 = n. No value constructor of `Plus` builds that for an `n` the checker knows nothing about, since both are about the first argument. `plusZeroRight(n)` does, by its own induction on `n`.",
      "On the second, `m` is `Succ(m1)`, `r` is `Succ(r1)` and `p1 : Plus(m1, n, r1)`, and Expected asks for `Plus(n, Succ(m1), Succ(r1))`. The recursive call `plusComm(m1, n, r1, subterm p1)` gives `Plus(n, m1, r1)`: n + m1 = r1. From that, `plusSucc` from the previous page gives n + (m1 + 1) = r1 + 1, which is what Expected asks for. Hover over `plusSucc` to see its parameters and returns.",
      "A call can be an argument of another call, so the whole branch can be a single expression, with the recursive call as the last argument of `plusSucc`."),
    task: replaceAll,
    refs: "§7, §8, §9, §12, §13",
    boxes: [box(nat, plusRel), box(plusZeroRight, plusSucc), plusCommLemma.goal],
    initial: `-- Replace each sorry(_).
${withQed(plusCommLemma.fn(gap, gap), "plusComm")}`,
    requireQed: true,
    solution: withQed(plusComm, "plusComm"),
  },
  {
    slug: "plus-assoc",
    title: "Associativity of addition",
    phase: 1,
    prose: paragraphs(
      "Associativity says that (a + b) + c and a + (b + c) are the same number. With `Plus`, every sum has to be named. Given ab with a + b = ab, and r with ab + c = r, the goal asks for a number bc with b + c = bc and a + bc = r. As with `r` on the page \"Appending vectors\", `bc` can be read as \"there is a `bc` such that\".",
      "Your box holds the whole proof, `qed` included, except for one branch. It is an induction on a, as a recursion on `p`. Read the `PlusSucc(a1, _, ab1, p1)` branch first, from the top.",
      "Put the caret on its first line, the pattern `let` on `q`. Scope shows what forcing `PlusSucc` told the checker: `a` is `Succ(a1)`, `ab` is `Succ(ab1)`, and so `q : Plus(Succ(ab1), c, r)`. A `PlusZero` would need `q`'s first argument to be `Zero()`, so it is refuted, as Refutations shows, and the pattern `let` is accepted. After it, `r` is `Succ(r1)` and `q3 : Plus(ab1, c, r1)`.",
      "The recursive call marks `p1` `subterm`, a strict subterm of `p`. It gives `bc`, `s1 : Plus(b, c, bc)` and `s2 : Plus(a1, bc, r1)`. On the last line, Expected asks for `Plus(Succ(a1), bc, Succ(r1))` as the third result, and `PlusSucc` turns `s2` into that. For now Scope marks `bc`, `s1` and `s2` as tainted: the call relies on the `sorry` still in `plusAssoc`.",
      "Now the `PlusZero` branch. On its `sorry(_)`, Scope shows that `a` is `Zero()` and `ab` is `b`, so `q : Plus(b, c, r)`. Expected asks for a `bc`, evidence of `Plus(b, c, bc)`, and evidence of `Plus(Zero(), bc, r)`. Choosing `bc` is up to you."),
    task: "Replace the `sorry(_)` in the `PlusZero` branch, until the status line reads \"No sorry\" and \"Goal proved\".",
    refs: "§7, §8, §9, §10, §12, §13",
    boxes: [box(nat, plusRel), plusAssocGoal],
    initial: `-- Replace the sorry(_) in the PlusZero branch.
${withQed(plusAssocWith(gap), "plusAssoc")}`,
    requireQed: true,
    solution: withQed(plusAssoc, "plusAssoc"),
  },
  {
    slug: "times-distrib",
    title: "Distributivity of multiplication",
    phase: 1,
    prose: paragraphs(
      "The last proof of this section puts the others to work. `Times(m, n, r)` is the claim that m × n = r. Like `Plus`, it is defined by cases on its first argument: 0 × n = 0, and if m × n = r and r + n = s, then (m + 1) × n = s.",
      "The goal is distributivity: a × (b + c) = a × b + a × c. With every number named, from `Plus(b, c, bc)` and `Times(a, bc, r)` it asks for `ab` and `ac` with `Times(a, b, ab)`, `Times(a, c, ac)` and `Plus(ab, ac, r)`.",
      "Your box holds the proof, an induction on a as a recursion on `t`, except for the `TimesZero` branch. Put the caret on its `sorry(_)`: Scope shows that `a` and `r` are `Zero()`, and Expected asks for `ab`, `ac`, `Times(Zero(), b, ab)`, `Times(Zero(), c, ac)` and `Plus(ab, ac, Zero())`. Zero times anything is zero.",
      "With the caret in the `TimesSucc` branch, Scope shows `t3 : Times(a1, bc, r1)` and `p1 : Plus(r1, bc, r)`: a1 × (b + c) = r1 and r1 + (b + c) = r. The recursive call gives `ab1` and `ac1` with a1 × b = ab1, a1 × c = ac1 and ab1 + ac1 = r1. Until the `sorry` is replaced, Scope marks what the call returns as tainted, as on the previous page.",
      "What is left is arithmetic on `Plus` alone. From (ab1 + ac1) + (b + c) = r, `exchange` produces `ab` and `ac` with ab1 + b = ab, ac1 + c = ac and ab + ac = r. The first two are the last fields `TimesSucc` needs to build `Times(Succ(a1), b, ab)` and `Times(Succ(a1), c, ac)`.",
      "`exchange`, in the fourth box, shows that (w + y) + (x + z) = (w + x) + (y + z). It has no recursion of its own: it chains associativity in both directions (`plusAssoc`, and `plusAssocRev`, proved by recursion on its second piece of evidence) and commutativity, all from the boxes above it.",
      "Each `let` in `exchange` writes the type of every value it binds, and the checker checks each type against the result it names. A type can mention a binder before it in the same `let`, such as `yxz`. A binder used that way needs a type of its own, which is why `yxz` carries `: Nat()`. Put the caret on each line of `exchange` and compare Scope with these types."),
    task: "Replace the `sorry(_)` in the `TimesZero` branch, until the status line reads \"No sorry\" and \"Goal proved\".",
    refs: "§6, §7, §8, §9, §12, §13",
    boxes: [box(nat, plusRel, times), box(plusZeroRight, plusSucc, plusComm), box(plusAssoc, plusAssocRev), exchange,
      timesDistribGoal],
    initial: `-- Replace the sorry(_) in the TimesZero branch.
${withQed(timesDistrib(gap), "timesDistrib")}`,
    requireQed: true,
    solution: withQed(timesDistrib(`
      (Zero(), Zero(), TimesZero(b), TimesZero(c), PlusZero(Zero()))`), "timesDistrib"),
  },
  {
    slug: "comptime",
    title: "Proof by reflection",
    phase: 1,
    prose: paragraphs(
      "Some claims are about one particular number that is easy to compute and tedious to prove by hand. Here `n` is ten times ten, computed by `times` in the second box, and the goal is `Even(n)`.",
      "Writing the evidence out does not work. `n` is the result of a call, and the checker knows a call's result only by its type: put the caret on your `let`, and Scope shows `n : Nat()` with no `is` rule. The run knows more: `print n;` shows one hundred `Succ`s around `Zero()`. Since the checker cannot tell whether `n` is `Zero()` or a `Succ`, neither `EvenZero()` nor an `EvenSucc` checks against the goal. And even for a number the checker does know, the evidence would be about a hundred nested value constructors.",
      "So let a program find the evidence. `decideEven`, in the first box, returns `Some` of evidence for `Even(n)` when `n` is even, and `None` otherwise. Your box takes its result apart with a pattern `let`, and that is an error: the result too is known only by its type, so forcing does not refute `None`.",
      "*`comptime`* fixes that. `comptime let Some(_, p) = e;` evaluates `e` while checking, and requires the value to be built by `Some`; if it is not, the error shows the value. The run, instead of forcing, rules out `None`, and `p` has type `Even(n)`. It is written only on a pattern `let`, and only at the top level.",
      "This does not seem to require trusting `decideEven`: whatever it returns inside `Some` has type `Even(n)`, because its returns say so and the checker checked its body. A proof like this is called a proof by reflection; one way to read the name is that a question about evidence is turned into a computation, and the computation's answer is turned back into evidence."),
    task: "Write `comptime` before the `let`, so that `qed p;` proves the goal. Then try `decideEven(Succ(Zero()))` in its place and read the error, which shows the value.",
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
      "Everything in this section rests on one promise: when the checker accepts a program and says \"Goal proved\", the goal really has evidence. If some accepted program could build a value of `False()`, every claim could be proved, and \"Goal proved\" would mean nothing. A checker with this promise is called sound.",
      "Languages like Pledge have known ways to break it. A function that calls itself forever could claim to return anything, `False()` included, without ever producing it. And Pledge has `Type() : Type()`: the type of all types is itself a type. In some languages that is enough to build a paradox that proves `False`.",
      "SOUNDNESS.md argues that neither reaches Pledge. It is a written argument by a Claude session, not machine-checked. Its reasons, in short: types never compute, since a type contains no function call; termination comes from the order of definitions and from `subterm` parameters, not from types; functions are not first class, so no type mentions one; and whether a value has a type is decided by recursion on the value. It notes that two known paradoxes, Curry's, and Girard's in Hurkens' form, seem to need function types over `Type()`, which cannot be written in Pledge.",
      "`loop` in your box is the first danger: it claims `False()` and only calls itself. The termination rule rejects the call, since `loop` has no `subterm` parameter. Marking `n` `subterm` does not help, since `n` is not a strict subterm of itself. Try other ways if you like: pass a function as an argument, or write a call in a type.",
      "The only way through that this tutorial knows is `sorry`. Then the program checks, but the `qed` relies on the `sorry`, and the goal is not proved."),
    task: "Make the program check, then read the status line.",
    refs: "§3, §4, §9, §12",
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
