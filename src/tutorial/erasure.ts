import type { Section } from "./pages.ts";
import { nat, vec, vheadBy } from "../examples.ts";
import { paragraphs, box, isZero, vecErased, vheadErased } from "./programs.ts";

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

const eqErased = `data Eq(A : Type(), x : A, y : A) : Type() {
  Refl(erased A : Type(), erased x : A) : Eq(A, x, x);
}`;

const castHead = `fn cast(erased m : Nat(), erased n : Nat(),
    erased p : Eq(Nat(), m, n), v : Vec(Nat(), m))
    -> (w : Vec(Nat(), n)) {`;

const castUse = `print cast(_, _, Refl(_, Succ(Zero())), VCons(_, _, Zero(), VNil(_)));
qed cast;
`;

const absurdHead = `fn f(erased n : Nat(), p : IsZero(n)) -> (r : Nat()) {
  match erased n : (r : Nat()) {
    Zero() => Zero();`;

const absurdUse = `  }
}
print f(Zero(), IsZeroHere());
`;

export const erasure: Section = { title: "Erasure", pages: [
  {
    slug: "erased",
    title: "Erasure",
    phase: 2,
    prose: paragraphs(
      "Look at `vhead` again. It takes the element type `A`, the length `n` and the vector `v`, but when it runs it looks only at `v`. `A` and `n` are there for the checker, so that it can turn away an empty vector. Once the program has been checked, nothing needs them. Much of what a dependent program passes around is like that.",
      "Pledge lets you say so. Its features come in *phases*, each adding to the one before, and the top of this page now says Phase 2: phase 2 adds erasure. Write `erased` before a binder's name, as in `erased n : Nat()`, and the binder is *erased*: the checker uses it as before, and evaluation skips it. The editor sets what evaluation skips in italics, starting with the erased binder itself.",
      "Java readers know the word. Java erases type arguments when it compiles, so a `List<String>` is a plain `List` when the program runs, and you have no say in it. In Pledge you choose what is erased, and the checker makes sure the program never needs it.",
      "So every binder now has a *multiplicity*, `many` or `erased`. That goes for parameters and returns, value-constructor fields, the binders of every kind of `let`, and the entries of a match's annotation. A binder is `many` unless you write `erased`, and the word goes right before the name, after `subterm` if there is one.",
      "An erased name can be used only where no value is needed when the program runs, such as in a type; the next page lists these places. So `Vec(A, Succ(n))` can mention an erased `A`, but passing an erased `A` on to a binder that is `many` is an error: evaluation would need a value that it skipped.",
      "Value constructors are never erased. A vector still records whether it is a `VNil` or a `VCons`, and `print` shows each erased field as `_`.",
      "In your box, `vcons` and `vsecond` already take `A` and `n` erased. The program is rejected at the first place one of them reaches a binder that is `many`: `VCons`'s field `A`, inside `vcons`. Read the error."),
    task: "Without changing `vcons` or `vsecond`, mark `VCons`'s fields `A` and `n` and `vhead`'s parameters `A` and `n` erased, so that the program checks. Erase `VNil`'s `A` too: nothing here requires it, but evaluation never uses it either. Then read what `print v;` shows, and put the caret inside `vsecond`: Scope tags `A` and `n` erased. The `A` and `n` that `vsecond` passes to `vhead` are now in italics too: they are arguments for erased parameters, so evaluation skips them.",
    refs: "§13, §16",
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
      "Evaluation skips an erased binder, so when the program runs there is no value for it. An erased name can therefore go only where no value is needed. The rule is there so that erasing a binder never changes what the program computes.",
      "Pledge lists these places, the erased positions: a type; an argument for an erased parameter or field; the result for an erased return or binder; and anything inside one of these. Anywhere else, an erased name is an error. The same goes for any erased result, such as what a call produces for an erased return.",
      "The editor shows you these places. Code in an erased position is set in italics, and so is each erased binder where it is bound: italic code is code that evaluation skips. Types are left upright, though every type is an erased position, because you can already see where a type is.",
      "Your box shows the error at its plainest. `len` promises that its result `m` is `n`, and returns `n`. As far as types go, that is right. But `n` is erased and `m` is not: when `len` runs, no caller has passed `n`, so there is nothing to return. The checker rejects the body at `n`, and the error names both sides, the erased `n` and `len`'s return `m`.",
      "There are two ways out, and they mean different things. You can erase the return, `erased m is n`: then `len`'s result is skipped as well, which is fine here, because the only place it goes is `let erased k`, an erased binder. Or you can stop erasing the parameter `n`, so that every call passes the length along when it runs. With the first, the whole body of `len` turns italic, since nothing it computes is kept. With the second, the body is upright. The line `let erased k = ...` is italic both ways.",
      "Either way, put the caret on the last line. Scope shows that `k` is `Succ(Zero())`, which is why `w : Vec(Nat(), k)` checks, and tags `k` erased, because its binder is `let erased k`."),
    task: "Make the program check one way, then the other. With each, add `print len(Nat(), Succ(Zero()), v);` at the end: the expression of a `print` is not an erased position, so after the first fix it is rejected, and after the second it shows `Succ(Zero())`.",
    refs: "§6, §13, §16",
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
      "Erased arguments are often obvious. In `vhead(Nat(), one, v)`, the type of `v` already says that its elements are `Nat()` and that its length is `Succ(one)`. Writing `Nat()` and `one` again adds nothing but a chance to get them wrong.",
      "In phase 2 you can write `_` for an erased argument, and the checker works it out by matching types. In `vhead(_, _, v)`, `vhead` asks for a `Vec(A, Succ(n))`, and `v` is a `Vec(Nat(), Succ(Succ(Zero())))`, so `A` must be `Nat()` and `n` must be `Succ(Zero())`. It works from the inside out too: in `VCons(_, _, Zero(), VNil(_))`, the head `Zero()` says that `A` is `Nat()`, and the type of `VNil(_)` says that `n` is `Zero()`.",
      "A `_` can also be worked out from what its position is given: in `let (e : Vec(Nat(), Zero())) = VNil(_);`, the binder's type says that `VNil`'s `A` is `Nat()`. These are the two sources: the other arguments, and what the position is given.",
      "Put the caret on a `_`. Expected shows the parameter it stands for, tagged erased, and the Term panel shows what the checker worked out for it, as does hovering over the `_`. Globals lists which parameters and fields are erased.",
      "A `_` has limits, each reported at the `_`. A `_` stands for an argument that is erased or whose type is `Type()`, or for part of a type you write, as in `let (e : Vec(_, Zero())) = VNil(Nat());`; anywhere else, as for `VCons`'s `head`, it is rejected. When nothing determines it, as in `print VNil(_);`, the program is rejected. A `_` in a call must be worked out by the time the call ends; one in an application of a value constructor or a type constructor can wait for what surrounds the application, up to the end of the call, statement, scrutinee or body it is in. And what a `_` stands for can mention only what exists before it, so a `_` that only the result of a later argument's call determines is rejected. A block passed as an argument counts as its final expression: `vhead(_, _, { v })` checks as `vhead(_, _, v)` does."),
    task: "Replace each erased argument with `_`, and check that the status line still reports the goal proved.",
    refs: "§8, §16",
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
      "Some arguments are proofs that only the checker needs. `cast`, in your box, turns a vector of length `m` into a vector of length `n`, given a proof `p` that `m` and `n` are equal. When it runs, the vector comes back unchanged; `p` is there only to convince the checker, so it is erased. But the checker learns that `m` and `n` are equal only by matching on `p`, and a match looks at its scrutinee.",
      "`match erased p : (...)` is a match whose scrutinee is erased, and the fields of each of its branches are erased too. A match written without `erased` is `many`. The scrutinee of a `many` match is not an erased position, so `match p` on the erased `p` is rejected at `p`.",
      "An erased match has a catch. Evaluation skipped `p`, so when the match runs it has no value to look at and cannot choose a branch. So if the match produces anything that is `many`, at most one of its branches can be one that runs, and evaluation runs that branch without looking. The italics show it: `erased p` and each branch's pattern are italic, and the body of the branch that runs is not.",
      "So `match erased n : (r : Nat()) { Zero() => Zero(); Succ(k) => k; }` is rejected at its second branch, while with `erased r` in the annotation it is allowed, since then it produces nothing that is `many`. The next page shows what a second branch is allowed to be.",
      "`cast` needs only one branch, for `Refl`. Forcing `Refl` equates `m` and `n`, so in that branch `v` has the type Expected asks for, and the branch is `v` itself. The goal is a function goal, as on the page \"Proof by recursion\". In phase 2 the multiplicities must agree too, so `cast` erases exactly the binders the goal erases."),
    task: "Replace `sorry(_)` with an erased match on `p`, with one branch. Put the caret in the branch: Scope shows that forcing `Refl` gave `n` the rule that it is `m`. The `print` then shows the vector, and the goal is proved.",
    refs: "§7, §10, §12, §13, §16",
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
    slug: "absurd-branches",
    title: "Absurd branches",
    phase: 2,
    prose: paragraphs(
      "An erased match has no value to choose a branch by, so at most one of its branches can run. In `cast` on the previous page that was easy: `Eq` has one value constructor. A match on an erased number has two to deal with, `Zero` and `Succ`.",
      "Sometimes forcing refutes one of them, and then it has no branch. But often a value constructor is ruled out only by a proof in scope, and as the page \"Refuting through a proof\" showed, it then still needs a branch: one that matches on the proof and finds every value constructor refuted.",
      "An erased match allows exactly that kind of extra branch. A branch whose body is a match with no branches is an *absurd branch*. (The body can also be a block that ends in such a match.) An absurd branch never runs, since no value can reach a match with no branches. So the rule is: an erased match that produces anything `many` has at most one branch that is not absurd, and evaluation runs that one.",
      "`f` in your box is the function of that earlier page, cut down: it returns a number in place of evidence, and it takes `n` erased, since its result never needs `n`. Its `Zero` branch is the one that runs. Its `Succ` branch is missing, and the error says so.",
      "Once your box checks, the `Succ` branch is all in italics, since it never runs. Put the caret on `match erased`: Refutations lists `Succ` as absurd. Put it on the inner `match p`: Refutations lists `IsZeroHere` as refuted, and opening it shows why. The `print` shows `Zero()`, from the branch that is not absurd.",
      "This is the end of the main path. You have written types that rule out mistakes, read types as claims, proved claims by recursion, and marked what only the checker needs. The appendix that follows is optional: each of its pages pins down one fine point of the rules.",
      "Three texts pick up where this one stops. \"Programming Language Foundations in Agda\", by Wadler, Kokke and Siek, begins with natural numbers, induction and relations, the ground you have just covered, in a language whose types compute. The Natural Number Game proves the lemmas of the section \"Arithmetic\" again in Lean, with tactics. \"Type-Driven Development with Idris\", by Edwin Brady, writes programs such as `vhead` in a language made for running them. They use other names for some of what you met here, and the glossary gives those names."),
    task: "Write the `Succ` branch as an absurd one: match on `p` there, with no branches.",
    refs: "§10, §13, §16",
    boxes: [box(nat, isZero)],
    initial: `-- Add the Succ branch: an absurd one, matching on p.
${absurdHead}
${absurdUse}`,
    requireQed: false,
    solution: `${absurdHead}
    Succ(m) => match p : _ {};
${absurdUse}`,
  },
] };
