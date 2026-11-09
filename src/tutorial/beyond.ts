import type { Section } from "./pages.ts";
import { nat } from "../examples.ts";
import { paragraphs, box, plus } from "./programs.ts";

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

export const beyond: Section = { title: "Beyond Pledge", pages: [
  {
    slug: "beyond",
    title: "What Pledge leaves out",
    phase: 1,
    prose: paragraphs(
      "You have proved real theorems the long way round. Languages such as Agda, Lean and Idris rest on the same ideas, with one large difference: in them, as far as this tutorial knows, types compute.",
      "In Pledge a type never contains a function call. That is why `plus` hands back a proof of `Plus(m, n, r)` beside its result, and why every fact about addition was a value of `Plus`. That seems to be what keeps the checker simple: it never runs anything while comparing types. Your box shows the cost. `print r;` shows four, but the checker knows `r` only as the result of a call, so `qed p;` is rejected: Scope shows that `p`'s type ends in `r`, and the error that the goal's ends in four. The run knows what the checker does not.",
      "So you take the steps. The first argument of `p`'s type is a `Succ`, so forcing refutes `PlusZero`, and `let PlusSucc(_, _, r1, p1) = p;` is accepted. After it, Scope shows that `r` is `Succ(r1)`. One such `let` for each step `plus` took brings `r` to four.",
      "Here is the same arithmetic in Agda, abridged from a file that was checked with Agda 2.6.3. The definitions of `two`, `four` and `cong`, and an import, are left out.",
      "```\n" + agda + "\n```",
      "`_+_` is an ordinary function, and `two + two` is written inside a type. `≡` is Agda's equality type, and `refl` plays the part of `Refl`. `twoPlusTwo` is `refl` because Agda's checker runs `two + two` while it compares the types: it takes the steps of your box unasked.",
      "It does not take every step. `zeroPlus` is `refl`, because `_+_` looks at its first argument, and `zero + n` becomes `n` by the first line of its definition. But `n + zero` is stuck on the unknown `n`, so `plusZero` needs an induction on `n`, like the one you wrote for `plusZero` on the page \"Proof by recursion\". With `refl` there, Agda reports `n + zero != n of type Nat`. The ideas carry over; what changes is how much the checker does unasked.",
      "Those languages have more, as this tutorial understands them. Functions are values there, so \"for every `n`, ...\" is itself a type, where Pledge has a function goal. Types sit in a hierarchy of levels, called universes, where Pledge has `Type() : Type()`. Pledge relies instead on three restrictions: a type contains no function call, functions are not values, and termination comes from the order of definitions and from `subterm`. SOUNDNESS.md, a written argument that is not machine-checked, argues that these suffice.",
      "What carries over unchanged, as far as this tutorial can tell: a type read as a claim and a value as its proof, matching that rules cases out, equality decided by comparing canonical forms, recursion as induction, and relations such as `Plus` declared as data types, which those languages use constantly.",
      "This is the end of the main path. The appendix that follows is optional: each of its pages pins down one fine point of the rules."),
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
