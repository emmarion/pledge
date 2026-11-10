import type { Section } from "./pages.ts";
import { nat, vec, vheadBy } from "../examples.ts";
import { paragraphs, box, eq, plusRel, plusEvidence, plus, gap, withQed } from "./programs.ts";

const numbers = `let one = Succ(Zero());
let two = Succ(one);
let three = Succ(two);
let four = Succ(three);
goal Plus(two, two, four);`;

const twoPlusTwo = (evidence: string): string => `let e : Plus(two, two, four) = ${evidence};
qed e;
let (s, q) = plus(two, two);
print s;
print q;
`;

const plusZero = (zero: string, succ: string): string =>
  `fn plusZero(subterm n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
    -> (e : Eq(Nat(), r, n)) {
  match p : _ {
    PlusZero(_) =>${zero};
    PlusSucc(m, _, r1, q) =>${succ};
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

export const relation: Section = { title: "Addition as a relation", pages: [
  {
    slug: "plus-relation",
    title: "Plus: addition as a type",
    phase: 1,
    prose: paragraphs(
      "The next claims are about addition, such as \"adding zero to a number gives the number back\". In Agda or Lean you would write `n + 0` right in the type, and the checker would run the addition while it compares types. Here that would be `Eq(Nat(), plus(n, Zero()), n)`, with a call to `plus` inside the type, and in Pledge you cannot write it: a type contains no function call, and writing one there is an error. That is deliberate. You build the sum as evidence instead, one step at a time, so every step the checker relies on is one you wrote and can read. The page \"What Pledge leaves out\" comes back to this, and to what it costs.",
      "Pledge describes addition by a type instead. `Plus(m, n, r)` is the claim that `m` plus `n` is `r`. Its value constructors are the two cases of addition: `PlusZero(n)` is evidence that zero plus `n` is `n`, and `PlusSucc(m, n, r, p)` turns evidence `p` that `m` plus `n` is `r` into evidence that `Succ(m)` plus `n` is `Succ(r)`. Compare them with the two branches of the function `plus` on the page \"Termination: subterm and same\": the same two cases, written as ways to build evidence. A type like `Plus`, which relates several values, is called a relation.",
      "The third box sets the goal `Plus(two, two, four)`, and your box starts its evidence as a `sorry(_)`. Build it as `plus` would compute. Two is `Succ(one)`, so the outer layer is a `PlusSucc`: it turns evidence that one plus two is three into evidence that two plus two is four. Write `PlusSucc(one, two, three, sorry(p : Plus(one, two, three)))`, then put the caret on the new `sorry` and go on. Expected names what each layer still owes.",
      "Nobody wants to write that out for large numbers, and nobody has to. The `plus` in the second box computes the sum as before, and builds the evidence alongside: it returns its result `r` together with `p : Plus(m, n, r)`. Its `Succ(k)` branch is a block, which binds the two results of the call for `k` and wraps one more layer around each.",
      "The last lines of your box call it. `print s;` shows four, and `print q;` shows the evidence you wrote by hand. Now put the caret on the last line and read Global entries: `s : Nat()`, with no rule, and `q : Plus(Succ(Succ(Zero())), Succ(Succ(Zero())), s)`. As on the page \"is binders\", the checker knows a call's results only by the function's returns. It does not know that `s` is four. It does know how `s` is related to the two arguments, and it has the evidence. The proofs on the next pages work from evidence like `q`."),
    task: "Replace `sorry(_)` with evidence that two plus two is four, until the status line reads \"No sorry\" and \"Goal proved\". Then put the caret on the last line, and compare what `print s;` shows with what Global entries shows about `s`.",
    refs: "§3, §5, §7, §8, §12, §13",
    boxes: [box(nat, eq, plusRel), plusEvidence, numbers],
    initial: `-- Replace sorry(_) with evidence that two plus two is four.
${twoPlusTwo("sorry(_)")}`,
    requireQed: true,
    solution: twoPlusTwo(`PlusSucc(one, two, three,
  PlusSucc(Zero(), two, two, PlusZero(two)))`),
  },
  {
    slug: "plus-zero",
    title: "Proof by recursion",
    phase: 1,
    prose: paragraphs(
      "Now a claim about every number at once: adding zero to a number gives the number back. You cannot check that by trying numbers; it takes a proof.",
      "With `Plus`, the claim reads: for every `n` and `r`, if `n` plus zero is `r`, then `r` equals `n`. The second box states it as a *function goal*: a function's parameters and returns, with no name and no body. Read it as \"for all such parameters there are such returns\". A function with the same parameters and returns proves it, and `qed plusZero;` names that function; on this page you write the `qed` yourself. The checker compares the two position by position; binder names and `subterm` marks need not agree.",
      "`plusZero` is a recursion on `n`, marked `subterm`, that takes apart the evidence `p`. A function that handles zero directly, and `Succ(m)` by calling itself on `m`, covers every number. Read as a proof, that is a proof by induction.",
      "Put the caret on the first `sorry(_)`. Scope shows that forcing `PlusZero` told the checker that `n` and `r` are both `Zero()`, and Expected asks for `e : Eq(Nat(), Zero(), Zero())`. One `Refl` does it.",
      "On the second `sorry(_)`, Scope shows that `n` is `Succ(m)`, `r` is `Succ(r1)` and `q : Plus(m, Zero(), r1)`, and Expected asks for `Eq(Nat(), Succ(r1), Succ(m))`. The call `plusZero(subterm m, r1, q)` gives evidence of `Eq(Nat(), r1, m)`. That is almost it, but a `Refl` needs the same term on both sides, and `r1` and `m` are different entries.",
      "So match on the evidence the call returns, as on the page \"Using an equality\". In the `Refl` branch the checker knows that `r1` is `m`, and Scope shows it. Expected is then `Eq(Nat(), Succ(m), Succ(m))`, and a `Refl` fits. While a `sorry` is left in `plusZero`, the call relies on it, and Scope reports the `Refl` branch as tainted by that call."),
    task: "Replace both `sorry(_)`, then write `qed plusZero;` below the function, until the status line reads \"No sorry\" and \"Goal proved\".",
    refs: "§7, §8, §9, §10, §12, §13",
    boxes: [box(nat, eq, plusRel), `goal fn (n : Nat(), r : Nat(), p : Plus(n, Zero(), r))
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
      "Appending puts one vector after another: lengths m and n give a vector of length m + n. The type of `vappend` should say so, as `vhead`'s type said \"not empty\". In some other languages you would write the result's type as `Vec(A, m + n)`. In Pledge you cannot, since a type contains no function call.",
      "So `vappend` does what `plus` does on the page \"Plus: addition as a type\", and the first box shows `plus` again: it returns the answer together with evidence. Its returns are a length `r`, evidence `p : Plus(m, n, r)`, and the vector `u : Vec(A, r)`. You can read them as \"there is an `r` such that m + n = r and `u` has length `r`\". The second box states this as a function goal. Here the goal is the function's own parameters and returns, so `qed vappend;`, already in your box, proves it as soon as no `sorry` is left.",
      "As `plus` is a recursion on `m`, `vappend` is a recursion on `v`, the first of the two vectors, marked `subterm`. Put the caret on the first `sorry(_)`: Scope shows that `m` is `Zero()` and `v` is `VNil(A)`, and Expected asks for `r : Nat()`, `p : Plus(Zero(), n, r)` and `u : Vec(A, r)`.",
      "On the second, Scope shows that `m` is `Succ(m1)` and `v` is `VCons(A, m1, x, rest)`, so `rest` is a strict subterm of `v`. Write the branch as `plus` writes its `Succ(k)` branch: a block whose tuple `let` binds the three results of `vappend(A, m1, n, subterm rest, w)`, say as `r1`, `p1` and `u1`. With a `sorry(_)` as the block's last expression, Scope there shows `p1 : Plus(m1, n, r1)` and `u1 : Vec(A, r1)`, marked tainted while a `sorry` is left in `vappend`.",
      "Then build the three results: one more on the length, a `PlusSucc` around the evidence, a `VCons` around the vector. Each element of the tuple has its own Expected, with the earlier ones filled in: after `Succ(r1)`, the second asks for `p : Plus(Succ(m1), n, Succ(r1))`.",
      "The run then prints three and the appended vector, but the checker knows less. Put the caret on the last line: Global entries shows `r : Nat()` with no rule and `u : Vec(Nat(), r)`. As on the page \"is binders\", the checker knows a call's results only by the function's returns. So the call `vhead(Nat(), two, u)`, which needs a vector of length three, is rejected. This is the price of stating addition as a relation; the page \"What Pledge leaves out\" comes back to it."),
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
] };
