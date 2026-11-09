import type { Section } from "./pages.ts";
import { nat, vec, vheadBy } from "../examples.ts";
import { paragraphs, box, vecErased, vheadErased } from "./programs.ts";

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

export const erasure: Section = { title: "Erasure", pages: [
  {
    slug: "erased",
    title: "Erasure",
    phase: 2,
    prose: paragraphs(
      "From this page on, programs are checked under phase 2, which adds erasure (§16). `vhead` returns the head of a vector; the type `A` and the length `n` are there so that the checker accepts `vhead` only on a vector that is not empty, but evaluating `vhead` never looks at them. A binder marked `erased` says so, and evaluation skips erased positions. Value constructors themselves are never erased, and every value built by one carries its tag, so a vector still says whether it is `VNil` or `VCons`; `print` shows an erased field as `_` (§16).",
      "Every binder has a multiplicity, `many` or `erased`: function parameters and returns, value-constructor fields, the binders of every kind of `let`, and match annotation entries. A binder is `many` unless written `erased` (§16). The multiplicity is written immediately before the binder's name, after any `subterm`, as in `erased n : Nat()` (§16). An erased name is allowed only in an erased position, such as a type or an argument for an erased parameter or field; the next page says more. Type-constructor arguments are always erased, so `Vec(A, Succ(n))` is allowed to mention an erased `A`.",
      "Here `vcons` and `vsecond` take `A` and `n` erased, and the program is rejected at the first place they are passed on to a binder that is `many`. Read the error. Once the program checks, put the caret inside `vsecond`: Scope tags `A` and `n` erased (§13), and in this implementation Expected tags an erased entry the same way."),
    task: "Without changing `vcons` or `vsecond`, mark binders `erased` so that the program checks: `VCons`'s fields `A` and `n`, and `vhead`'s parameters `A` and `n`. `VNil`'s `A` is not used by evaluation either; nothing here requires it, but it is natural to erase it too. Then read what `print v;` shows.",
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
      "§16 allows an erased name only in an erased position: a type, an argument for an erased parameter or field, the result for an erased return or binder, and everything inside these. Anywhere else it is an error. In this implementation the same holds for any erased result, such as a call's result for an erased return.",
      "`len` says that its result `m` is `n` (§6), and returns `n`. But `n` is erased, and the result for the `many` return `m` is not an erased position, so the checker rejects the body at `n`: evaluation skips the argument for `n`, so when `len` runs there is no value of `n` to return.",
      "There are two ways out. Mark the return `erased m is n`: `len`'s result is then erased, and the `let erased k` that binds it is an erased position, which evaluation skips. Or stop erasing the parameter `n`, so that every call passes it. Either way, Scope on the last line shows that `k` is `Succ(Zero())`, so the binder `w : Vec(Nat(), k)` checks, and tags `k` erased, which in this implementation follows from its binder `let erased k`."),
    task: "Make the program check, either way, then try the other. Then add `print len(Nat(), Succ(Zero()), v);`: in this implementation the expression of a `print` is not an erased position, so after the first fix it is rejected, and after the second it shows `Succ(Zero())`.",
    refs: "§6, §16",
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
      "In phase 2, `_` also stands for an erased argument, solved by unification (§16). In `vhead(_, _, VCons(_, _, Zero(), VNil(_)))`, the head `Zero()` fixes the inner `A` as `Nat()`, the type of `VNil(_)` fixes the inner `n` as `Zero()`, and the vector's type then fixes `vhead`'s `A` and `n`. In this implementation a `_` is also solved from what its position is given (§8): in `let (e : Vec(Nat(), Zero())) = VNil(_);`, the binder's type fixes `VNil`'s `A`.",
      "In this implementation, `_` is allowed only as a whole argument of a call or application in an expression, for an erased parameter or field or a type constructor's argument; not inside a type written in a binder, such as `Vec(_, n)`. Globals shows which parameters and fields are erased. Put the caret on a `_`: Expected shows the parameter it stands for, tagged erased. Click a `_` to see its solution, canonicalized.",
      "When nothing determines a `_`, as in `print VNil(_);`, the program is rejected. This implementation has a further limit: a `_`'s solution must mention only entries created before the `_`, so a `_` that only a later argument's call result determines is rejected. A block used as an argument takes part in solving through its final expression, as a direct argument does: `vhead(_, _, { v })` checks as `vhead(_, _, v)` does."),
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
      "`match erased e : (...)` takes its scrutinee erased; a match written without a multiplicity is `many`. In an erased match, every field of a branch is bound erased (§16). In this implementation the scrutinee of a `many` match is not an erased position, so `match p` on an erased `p` is rejected at `p`.",
      "An erased match with a `many` annotation entry has at most one branch that is not absurd, a branch being absurd when its body is a match with no branches (§16). Evaluation skips the erased scrutinee, so it has no tag to choose a branch by; with only one branch that is not absurd there seems to be nothing to choose. SOUNDNESS.md part 9, which argues erasure only in outline, relies on this. So `match erased n : (r : Nat()) { Zero() => Zero(); Succ(k) => k; }` is rejected at its second branch, while with `erased r` it is allowed. In this implementation the rule applies even to a match that never runs.",
      "`cast` turns a vector of length `m` into one of length `n`, given a proof `p` that `m` and `n` are equal, which matters only to the checker and so is erased. An erased match on `p` forces `Refl`, which equates `m` and `n` (§7), so in its one branch `v` has the type Expected asks for, and evaluation simply returns `v`. The goal is a function goal, as on the \"Proof by recursion\" page; in phase 2 multiplicities must agree too (§12), so `cast`'s binders are erased exactly where the goal's are."),
    task: "Replace `sorry(_)` with an erased match on `p`. Put the caret in its branch: Scope shows that forcing `Refl` added the rule that `n` is `m`. Then the `print` shows the vector, and the goal is proved.",
    refs: "§7, §12, §16",
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
] };
