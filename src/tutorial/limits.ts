import type { Section } from "./pages.ts";
import { nat } from "../examples.ts";
import { paragraphs, box, evenOdd, plusFn, plus, falseType } from "./programs.ts";

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

const explode = `fn explode(A : Type(), f : False()) -> (x : A) {
  match f : _ {}
}`;

export const agda = `data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
_+_ : Nat → Nat → Nat
zero  + n = n
suc m + n = suc (m + n)
twoPlusTwo : (two + two) ≡ four
twoPlusTwo = refl
zeroPlus : (n : Nat) → (zero + n) ≡ n
zeroPlus n = refl
plusZero : (n : Nat) → (n + zero) ≡ n
plusZero zero    = refl
plusZero (suc k) = cong suc (plusZero k)`;

export const limits: Section = { title: "Limits and guarantees", pages: [
  {
    slug: "comptime",
    title: "Proof by reflection",
    phase: 1,
    prose: paragraphs(
      "Some claims are about one particular number that is easy to compute and tedious to prove by hand. Here `n` is ten times ten, computed by `times` in the second box, and the goal is `Even(n)`.",
      "Writing the evidence out does not work. `n` is the result of a call, and the checker knows a call's result only by its type: put the caret on your `let`, and Scope shows `n : Nat()` with no `is` rule. The run knows more: `print n;` shows one hundred `Succ`s around `Zero()`. Since the checker cannot tell whether `n` is `Zero()` or a `Succ`, neither `EvenZero()` nor an `EvenSucc` checks against the goal. And even for a number the checker does know, the evidence would be about a hundred nested value constructors.",
      "So let a program find the evidence. `decideEven`, in the first box, returns `Some` of evidence for `Even(n)` when `n` is even, and `None` otherwise. Your box takes its result apart with a pattern `let`, and that is an error: the result too is known only by its type, so forcing does not refute `None`.",
      "*`comptime`* fixes that. `comptime let Some(_, p) = e;` evaluates `e` while checking, and requires the value to be built by `Some`; if it is not, the error shows the value. The run, instead of forcing, rules out `None`, and `p` has type `Even(n)`. It is written only on a pattern `let`, and only at the top level.",
      "This does not require trusting `decideEven`: whatever it returns inside `Some` has type `Even(n)`, because its returns say so and the checker checked its body. A proof like this is called a proof by reflection; one way to read the name is that a question about evidence is turned into a computation, and the computation's answer is turned back into evidence."),
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
    title: "Soundness",
    phase: 1,
    prose: paragraphs(
      "Every proof in this tutorial rests on one promise: when the checker says \"Goal proved\", the claim really has evidence. A checker that keeps this promise is called *sound*.",
      "The promise is all or nothing. `False()` has no value constructors, so there should never be a value of it. Suppose one got through anyway. `explode`, in the first box, takes any type `A` and a `False()`, and returns a value of `A`: its match on the `False()` has no branches, so it can promise anything. With one value of `False()`, `explode` gives evidence that zero is one, that three is even, of every claim there is. \"Goal proved\" would then mean nothing. So the whole job of soundness is to keep a value of `False()` from being built.",
      "How could you try to build one? A value is built by value constructors, and `False()` has none, so not directly. That leaves three ways to cheat, and you have already met what stops each.",
      "The first is never to answer. `loop` in your box promises a `False()` and only calls itself. It never has to produce one, because it never returns. The termination rule stops this: a function calls itself only on a strict subterm, and a value can be taken apart only finitely many times, so every call returns. Marking `n` `subterm` does not help `loop`, since `n` is not a strict subterm of itself.",
      "The second is to skip a case. A match with no branches promises anything, as in `explode`, so `loop` could try `match n : _ {}`. But `n` is a number, and a number is built by `Zero` or by `Succ`. Every value constructor needs a branch, and the checker drops one only when forcing it ends in a contradiction, which you can read under Refutations. A branch you do write must still produce a `False()`.",
      "The third is to leave a gap. `sorry` produces a value of any type, `False()` included. Pledge allows that and keeps the books: whatever relies on a `sorry` is tainted, and a tainted `qed` does not prove the goal.",
      "Other proof languages have the same three defences, under names such as termination checking and coverage checking. They face a fourth danger, which Pledge avoids by being small. Where functions are values and types can compute, a type can be made to talk about itself, as the sentence \"this sentence is false\" does, and those languages need further rules to prevent it. In Pledge a function is not a value and a type contains no function call, so there is nothing to build such a type from.",
      "Readers who want the full argument that these defences are enough will find it in SOUNDNESS.md."),
    task: "Try each cheat as the body of `loop`, and read what stops it: first `loop(n)`, as given; then `match n : _ {}`; then `sorry(_)`, which checks. Then read the status line.",
    refs: "§3, §4, §9, §10, §12",
    boxes: [box(nat, falseType, explode), "goal False();"],
    initial: `-- Try each cheat as the body of loop. Can you prove the goal?
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
    slug: "beyond",
    title: "What Pledge leaves out",
    phase: 1,
    prose: paragraphs(
      "You have proved real theorems the long way round. Languages such as Agda, Lean and Idris rest on the same ideas, with one large difference: in them, types compute.",
      "In Pledge a type never contains a function call. That is why `plus` hands back a proof of `Plus(m, n, r)` beside its result, and why every fact about addition was a value of `Plus`. That keeps the checker simple: it never runs anything while comparing types. Your box shows the cost. `print r;` shows four, but the checker knows `r` only as the result of a call, so `qed p;` is rejected: Scope shows that `p`'s type ends in `r`, and the error says that the goal's ends in four. The run knows what the checker does not.",
      "So you take the steps. The first argument of `p`'s type is a `Succ`, so forcing refutes `PlusZero`, and `let PlusSucc(_, _, r1, p1) = p;` is accepted. After it, Scope shows that `r` is `Succ(r1)`. One such `let` for each step `plus` took brings `r` to four.",
      "Here is the same arithmetic in Agda, abridged from a file that was checked with Agda 2.6.3. The definitions of `two`, `four` and `cong`, and an import, are left out.",
      "```\n" + agda + "\n```",
      "`_+_` is an ordinary function, and `two + two` is written inside a type. `≡` is Agda's equality type, and `refl` plays the part of `Refl`. `twoPlusTwo` is `refl` because Agda's checker runs `two + two` while it compares the types: it takes the steps of your box unasked.",
      "It does not take every step. `zeroPlus` is `refl`, because `_+_` looks at its first argument, and `zero + n` becomes `n` by the first line of its definition. But `n + zero` is stuck on the unknown `n`, so `plusZero` needs an induction on `n`, like the one you wrote for `plusZero` on the page \"Proof by recursion\". With `refl` there, Agda reports `n + zero != n of type Nat`. The ideas carry over; what changes is how much the checker does unasked.",
      "Those languages have more. Functions are values there, so \"for every `n`, ...\" is itself a type, where Pledge has a function goal. In Agda and Lean, types sit in a hierarchy of levels, called universes, where Pledge has `Type() : Type()`. Pledge relies instead on three restrictions: a type contains no function call, functions are not values, and termination comes from the order of definitions and from `subterm`. SOUNDNESS.md argues that these suffice.",
      "What carries over unchanged: a type read as a claim and a value as its proof, matching that rules cases out, equality decided by comparing canonical forms, recursion as induction, and relations such as `Plus` declared as data types, which those languages use constantly. The page \"Absurd branches\", the last of the main path, names three texts to go on with.",
      "This is the end of phase 1 of Pledge. The next section turns on phase 2, which adds one feature: erasure, a way to say which parts of a program are there only for the checker."),
    task: "Before the `qed`, take `p` apart with one pattern `let` for each step `plus` took, and watch `r` in Scope after each. Put the caret on `PlusSucc` in the first `let`: Refutations lists `PlusZero`, and opening it shows why it is ruled out.",
    refs: "§3, §4, §7, §9, §10, §12",
    boxes: [box(nat, plus), `let two = Succ(Succ(Zero()));
let four = Succ(Succ(two));
let (r, p) = plus(two, two);
print r;
goal Plus(two, two, four);`],
    initial: `-- Take p apart one step at a time, then prove the goal.
qed p;
`,
    requireQed: true,
    solution: `let PlusSucc(_, _, r1, p1) = p;
let PlusSucc(_, _, r2, p2) = p1;
let PlusZero(_) = p2;
qed p;
`,
  },
] };
