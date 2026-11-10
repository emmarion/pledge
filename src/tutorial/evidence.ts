import type { Section } from "./pages.ts";
import { nat } from "../examples.ts";
import { paragraphs, box, evenOdd, eq, isZero, falseType } from "./programs.ts";

const four = `let three = Succ(Succ(Succ(Zero())));
let four = Succ(three);
goal Even(four);`;

const fourIsEven = (proof: string): string => `let p : Even(four) = ${proof};
print p;
qed p;
`;

const succBoth = (body: string): string => `fn succBoth(a : Nat(), b : Nat(), e : Eq(Nat(), a, b))
    -> (f : Eq(Nat(), Succ(a), Succ(b))) {
  ${body}
}
`;

const isZeroEq = (succBranch: string): string => `fn f(n : Nat(), p : IsZero(n)) -> (e : Eq(Nat(), n, Zero())) {
  match n : _ {
    Zero() => Refl(Nat(), n);${succBranch}
  }
}
`;

export const evidence: Section = { title: "Evidence", pages: [
  {
    slug: "evidence",
    title: "Evidence: Even and Odd",
    phase: 1,
    prose: paragraphs(
      "On the page \"Mutual groups\", `isEven(two)` printed `Yes()`. That is an answer, and to believe it you have to trust that `isEven` was written correctly. This page shows a second way to say that two is even, which the rest of the tutorial builds on: a type that states the fact.",
      "The first box declares two types, `Even(n)` and `Odd(n)`, in a `mutual` block, since each mentions the other. Look at what their value constructors build. `EvenZero()` is an `Even(Zero())`. `EvenSucc(n, p)` takes a `p` of type `Odd(n)` and is an `Even(Succ(n))`, and `OddSucc` does the same the other way round. These follow the definition of even and odd, and there is no other way to build either type. So a value of type `Even(n)` exists only when `n` is even.",
      "That makes `Even(n)` a claim, \"`n` is even\", and a value of the type evidence that the claim holds. To show that a claim is true, you write a value of its type, and the checker checks it. No value has type `Even(Succ(Zero()))`, since no combination of the value constructors builds one. So nothing shows that one is even, as long as you leave out `sorry`, which the next page introduces. This way of reading types is known as propositions as types.",
      "A value of type `Even(two)` asks for less trust than the answer `Yes()` did: the declaration of `Even` is all there is to read, and the checker checks the value against it. In Java terms, `isEven` is a method `boolean isEven(int n)`: it answers `true`, and the answer carries nothing of why. A value of type `Even(n)` is the reasoning itself, and the checker has read it.",
      "The second box ends with `goal Even(two);`. A *goal* states the claim a program sets out to prove: the type it means to give a value of. A *`qed`* statement, `qed e;`, offers `e` as that value, and the checker checks `e` against the goal. A program has at most one of each, at the top level, with the `qed` after the `goal`. Build the evidence from the inside out: `EvenZero()` for zero, an `OddSucc` around it for one, an `EvenSucc` around that for two. Each of the two takes, as its first argument, the number it steps up from.",
      "The status line under your box reads \"No qed in your box\" and \"Goal not proved\"; once your `qed` checks, \"qed checks\" and \"Goal proved\"."),
    task: "Prove the goal: write a `qed` with evidence that two is even.",
    refs: "§5, §12",
    boxes: [box(nat, evenOdd), `let two = Succ(Succ(Zero()));
goal Even(two);`],
    initial: `-- Prove the goal: write qed with evidence that two is even.
`,
    requireQed: true,
    solution: `qed EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()));
`,
  },
  {
    slug: "sorry",
    title: "sorry and taint",
    phase: 1,
    prose: paragraphs(
      "The proofs from here on are longer, and you will not write them in one go. You need a way to leave a gap, have the rest checked anyway, and see what belongs in the gap.",
      "*`sorry`* is that gap. `sorry(q : Odd(three))` is a value of type `Odd(three)` with nothing behind it. Inside the parentheses is a telescope, as after a function's arrow, so one `sorry` can stand for several values. Checking goes on past it as past any other expression.",
      "Usually you need not write the telescope. `sorry(_)` takes it from where it stands: it is the same `_` as on the page \"_ for match annotations\", allowed at the same places, such as the right-hand side of `let p : Even(four)` in your box. Put the caret on `sorry(_)`: Expected shows `p : Even(Succ(Succ(Succ(Succ(Zero())))))`, the gap's type, and Local entries shows what you can use to fill it. Hovering over the `_` shows the same telescope. An argument is not such a place, so there you write the telescope out.",
      "A `sorry` proves nothing, so nothing built from it should count. The checker records what relies on a `sorry`, and calls this *taint*. Here `p` is tainted: put the caret on the `print` line, and Global entries marks it. A tainted result is not evaluated, so `print p;` shows `sorry`. The `qed` still checks, since the types fit, but the goal is not proved. The status line says so: \"Contains sorry\", \"qed checks\", \"Goal not proved\".",
      "This is how to work on the longer pages that follow. They start with `sorry(_)` in every gap you are to fill. Put the caret on a gap, read Expected and Local entries, and replace it. You are done when the status line reads \"No sorry\" and \"Goal proved\"."),
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
    slug: "equality",
    title: "Equality",
    phase: 1,
    prose: paragraphs(
      "Most claims worth proving say that two things are equal: this sum is that number, this vector is that one. So equality gets a type of its own, and the first box declares it.",
      "`Eq(A, x, y)` is the claim that `x` and `y`, two values of type `A`, are equal. It has one value constructor, `Refl(A, x)`, and its type is `Eq(A, x, x)`, with the same `x` on both sides. So a `Refl` is evidence that two terms are equal when the checker sees the same canonical form on both sides. (`Refl` is short for reflexivity: everything equals itself.)",
      "Nothing about `Eq` is built in. It is an ordinary `data` declaration, and it means equality because of the way the checker compares terms, which you watched on the page \"What the checker knows\".",
      "The second box ends with `goal Eq(Nat(), two, Succ(Succ(Zero())));`, and on this page you write the `qed`. `Refl(Nat(), two)` has type `Eq(Nat(), two, two)`. Does that fit the goal? The checker compares canonical forms, and `two` canonicalizes to `Succ(Succ(Zero()))`. Put the caret on `two` in the `goal` line: the Term panel shows the rewrites. If the types do not fit, the error names both."),
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
    slug: "eq-use",
    title: "Using an equality",
    phase: 1,
    prose: paragraphs(
      "Evidence can be an input as well as an output. `succBoth` takes evidence `e` that `a` equals `b`, and returns evidence that `Succ(a)` equals `Succ(b)`. Read a function like this as \"if ..., then ...\": whoever has values for the parameters gets the returns. This one says that if two numbers are equal, so are the numbers after them.",
      "Put the caret on `sorry(_)`. Expected asks for `f : Eq(Nat(), Succ(a), Succ(b))`. A `Refl` has the same term on both sides, and here the two sides differ: Local entries shows `a` and `b` as two entries with no rule, so the checker has no reason to think that they are the same. Try `Refl(Nat(), Succ(a))` in place of the `sorry(_)`. The error says that it has type `Eq(Nat(), Succ(a), Succ(a))`.",
      "The evidence `e` is in scope, but the checker does not use it by itself. To use evidence, you take it apart. So match on `e`. Its type has one value constructor, `Refl(A, x)`, of type `Eq(A, x, x)`. Forcing `Refl` supposes that `e` was built by it, so `e`'s type, `Eq(Nat(), a, b)`, would have to be `Eq(A, x, x)` for some `x`: both `a` and `b` are that one `x`. Unlike the forcing that refuted `VNil`, this ends in no contradiction. It ends in a fact.",
      "Write `match e : _ { Refl(_, _) => sorry(_); }` and put the caret on the new `sorry(_)`. Local entries shows `b : Nat() is a`: inside the branch, `b` has the rule that it is `a`. Expected now asks for `Eq(Nat(), Succ(a), Succ(a))`, because the checker shows, and compares, canonical forms. The `Refl` that was rejected a moment ago fits.",
      "This is how an equality is used in Pledge: match on it, and inside the branch its two sides are one. Since `Refl` is the only value constructor of `Eq`, a pattern `let` does the same in one line, `let Refl(_, _) = e;`, and the rest of the block knows the fact. The proofs on later pages do this again and again."),
    task: "Replace `sorry(_)` with a match on `e` whose one branch returns a `Refl`, until the status line reads \"No sorry\". Then write the body again with a pattern `let` in place of the match.",
    refs: "§7, §8, §10, §12, §13",
    boxes: [box(nat, eq)],
    initial: `-- Replace sorry(_): match on e, and return a Refl in its branch.
${succBoth("sorry(_)")}`,
    requireQed: false,
    solution: succBoth(`match e : _ {
    Refl(_, _) => Refl(Nat(), Succ(a));
  }`),
  },
  {
    slug: "empty",
    title: "Empty types and False()",
    phase: 1,
    prose: paragraphs(
      "Some things you want to prove are negative: zero is not one, an empty list has no first element. To say \"this cannot happen\" with a type, you need a type that has no values.",
      "The first box declares one: `False()`, with no value constructors at all, so no value of it can be built. A type like this is called an empty type.",
      "A function that returns `False()` can be read as evidence that its parameters cannot all have values: if they had, the function would produce a value of `False()`, and there is none. `zeroNotOne` in your box takes evidence that `Zero()` equals `Succ(Zero())` and returns `False()`. So it shows that zero is not one.",
      "How can its body produce a `False()`? It does not have to. The `match` on `e` needs a branch for each value constructor of `Eq` that is not refuted, and `Refl` is refuted. On the previous page, forcing `Refl` made two entries the same. Here it cannot: if `e` were a `Refl`, `Zero()` and `Succ(Zero())` would have to be the same value. So the match has no branches. With no branch to check, it can promise any telescope after the colon. That is how `absurd`, in the second box, turns a `False()` into a `Nat()`, and so into anything else.",
      "This is why it matters that no accepted program builds a value of `False()`: with one, `absurd` and its like would prove every claim. The page \"Soundness\", later on, shows what keeps one from being built."),
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
      "Evidence can also rule a case out, though not by itself. `f` in your box takes a number `n` and evidence `p : IsZero(n)`, and returns evidence that `n` equals `Zero()`. `IsZero`, in the first box, has one value constructor, `IsZeroHere()`, of type `IsZero(Zero())`, so a value of `IsZero(n)` can only be built when `n` is zero.",
      "You might expect the match on `n` to need no branch for `Succ`, since `p` rules it out. It does need one, and the error says so. The checker refutes a value constructor only by what it knows about the scrutinee, `n`, and its type. `p` is neither, so it does not refute anything by itself. The rule keeps refutation easy to follow: the checker never searches the scope for evidence, and you choose which evidence to take apart.",
      "So write the `Succ(m)` branch. It is to produce `Eq(Nat(), Succ(m), Zero())`, which `Refl` cannot build. But forcing `Succ` told the checker that `n` is `Succ(m)`, so in that branch Local entries shows `p : IsZero(Succ(m))`. A match on `p` there refutes `IsZeroHere`, whose type is `IsZero(Zero())`.",
      "That match has no branches, so, like the match in `zeroNotOne` on the previous page, it can produce whatever its annotation says. As for the match on `n`, write `_` as the annotation."),
    task: "Add the `Succ(m)` branch: a match on `p` with no branches. Then put the caret on that `match` and open `IsZeroHere` under Refutations.",
    refs: "§7, §10, §13",
    boxes: [box(nat, eq, isZero)],
    initial: `-- Add the Succ branch: a match on p there, with no branches.
${isZeroEq("")}`,
    requireQed: false,
    solution: isZeroEq(`
    Succ(m) => match p : _ {};`),
  },
] };
