import type { Section } from "./pages.ts";
import { nat, vec } from "../examples.ts";
import { paragraphs, box, eq, vecErased, vheadErased } from "./programs.ts";

const pair = `fn pair(x : Nat()) -> (n : Nat(), v : Vec(Nat(), Succ(n))) {
  (Zero(), VCons(Nat(), Zero(), x, VNil(Nat())))
}`;

const escaped = `let (n, v) = pair(Succ(Zero()));
let h = { let VCons(_, _, hd, tl) = v; hd };
inspect;`;

const escapedGoal = "goal Eq(Vec(Nat(), Succ(n)), v, VCons(Nat(), n, h, t));";

const taintedLet = (scrutinee: string): string => `let v = ${scrutinee};
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

export const appendix: Section = { title: "Appendix: fine points", appendix: true, pages: [
  {
    slug: "tuple-let-telescope",
    title: "A let's binders as a telescope",
    phase: 1,
    prose: paragraphs(
      "This appendix is optional. Each of its pages takes one rule and shows exactly where its edges are, for readers who want to know, and cites the section of DESIGN.md that states it, as §6 below. One page, \"_ through a block\", shows behaviour of this implementation on which DESIGN.md is silent.",
      "When one result's type depends on another, a `let` that states the type of every result it binds needs a later type to mention an earlier binder, as `exchange` on the page \"Distributivity of multiplication\" does. The binders of a tuple `let` are a telescope (§6), which is what makes this work: a binder's type or `is` clause can refer to the binders before it. In `let (m : Nat(), v : Vec(Nat(), Succ(m))) = pair(x);`, `v`'s type mentions `m`.",
      "The `let` gives its right-hand side its binders, so `v`'s type is checked with `m` standing for the call's first result, as a function's returns are checked with the earlier returns standing for its results (§8).",
      "Put the caret on the right-hand side, `pair(x)`: Expected lists both binders, the second mentioning the first (§13). On the `print` line, Global entries shows `v : Vec(Nat(), Succ(m))`."),
    task: "Delete `: Nat()` from `m`'s binder and read the error. §6 does not allow a type or `is` clause to refer to a binder that carries neither; in this implementation the error is at the reference, the `m` in `v`'s type, saying that `m` has no type there. Then put the type back so that the program checks again.",
    refs: "§6, §8, §13",
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
    title: "Facts outlive names",
    phase: 1,
    prose: paragraphs(
      "A block can return what a pattern `let` inside it took apart: in box 2, `h` names the very entry that forcing created for the field `hd` (§8). After the block, the checker still knows how that entry relates to `v`, and this page shows why.",
      "A pattern `let`'s names are in scope for the rest of the enclosing block, but its fields and facts last to the end of the enclosing match branch or function body, or of the program (§7, §10). So what forcing learned inside a block is still known after it, though the names the pattern gave are gone. A match branch is different: its facts depend on which value constructor the branch is for, so they cannot outlast it.",
      "Look at the `inspect;` at the end of box 2, or put the caret on its line and open Global entries. It shows `v`'s rule, `VCons(Nat(), n, h, ...)`, still in force. The field `hd` appears as `h`, the name the tuple `let` gave its entry. The tail, which the pattern named `tl`, appears as a marker beginning `?@`: an entry with no name, the field `rest` of a forced `VCons`, linked to the `tl` where it was created (§13). The entry is there; the name is not."),
    task: "The goal is that `v` is the `VCons` of `h` and a tail `t`. Bind `t` with a second pattern `let` on `v` before the goal, then prove it with `qed`. It checks only because the block's fact escaped: forcing the second pattern `let` equates `v`'s known `VCons` with the new one, so its head is `h`.",
    refs: "§7, §8, §10, §13",
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
    slug: "tainted-pattern-let",
    title: "A tainted pattern let",
    phase: 1,
    prose: paragraphs(
      "Your box has the previous page's shape, but `v` comes from `sorry`. Forcing `VCons` on it adds facts that nothing backs. Such a fact can make later code check that otherwise would not, such as an `is` clause or a `qed`, so for soundness everything those facts reach is treated as relying on the `sorry`.",
      "They reach as far as any pattern `let`'s facts: to the end of the enclosing match branch or function body, or of the program (§7). So a pattern `let` whose scrutinee is tainted taints every result of the match branch or function body it is in, or, at the top level, every result of the top-level statements after it (§12). After it, at the top level, nothing evaluates, every `print` shows `sorry` and no `qed` proves the goal, though checking goes on.",
      "Every statement in your box checks, yet the status line reports \"Goal not proved\", and `print n;` shows `sorry`, although `n` has nothing to do with `v` and box 2 printed it. Put the caret after the pattern `let`: Local entries says that the scope is tainted and links to the scrutinee, while `n` itself has no `tainted` tag.",
      "Box 2 has the same pattern `let` inside a match branch. There its facts end with the branch, and it taints only the match's results: `print c;` shows `sorry`, while `print n;` after it shows `Zero()` (§12)."),
    task: "Replace the `sorry` with a real vector of type `Vec(Nat(), Succ(Zero()))`, so that the goal is proved. The status line still reports `sorry` in the program, from the box above yours.",
    refs: "§7, §12",
    boxes: [box(nat, vec, eq, pair), inBranch],
    initial: `-- Replace the sorry with a real vector, so that the goal is proved.
-- Keep the pattern let on v.
${taintedLet("sorry(v : Vec(Nat(), Succ(Zero())))")}`,
    requireQed: true,
    solution: taintedLet("VCons(Nat(), Zero(), Zero(), VNil(Nat()))"),
  },
  {
    slug: "hole-through-block",
    title: "_ through a block",
    phase: 2,
    prose: paragraphs(
      "Wrapping an argument in a block could leave a `_` that nothing solves. DESIGN.md is silent on this case. §8 says a block gives its final expression what the block is given, and this implementation reads an argument the same way.",
      "So a block used as an argument takes part in solving the call's `_`s through its final expression, as a direct argument does; the block's statements do not, nor does a match branch's body. `vhead(_, _, { v })` checks as `vhead(_, _, v)` does: `v`'s type, `Vec(Nat(), Succ(Zero()))`, is matched against the parameter's, `Vec(A, Succ(n))`.",
      "Once your box uses `_`, put the caret on each `_`: Expected shows the parameter it stands for, tagged erased, and the Term panel shows its solution: `Nat()` for `A` and `Zero()` for `n`."),
    task: "Replace `vhead`'s erased arguments with `_` in both calls, and check that both still print.",
    refs: "§8",
    boxes: [box(nat, vecErased, vheadErased), `let one = Succ(Zero());
let v = VCons(_, _, one, VNil(_));`],
    initial: `-- Replace vhead's erased arguments with _ in both calls.
${throughBlock("Nat()", "Zero()")}`,
    requireQed: false,
    solution: throughBlock("_", "_"),
  },
  {
    slug: "hole-taint",
    title: "_ and taint",
    phase: 2,
    prose: paragraphs(
      "Writing `_` where a tainted argument belongs does not hide the taint: a `_` is tainted when the term it is solved to mentions a tainted entry (§12). Without that rule, a call relying on a `sorry` could prove a goal.",
      "Here `count`'s parameter has type `Vec(A, Zero())`, and `A` comes from `sorry`, so the `_` in `VNil(_)` is solved to `A` and is tainted, and so is the call, as it would be with `VNil(A)` written out.",
      "Put the caret on either `_`: the Term panel shows its solution, `A`. The status line reports \"qed checks\" and \"Goal not proved\", and the `print` shows `sorry`."),
    task: "Replace `sorry(A : Type())` with `Nat()`. The `_` is then solved to an untainted entry, the `print` shows `Zero()`, and the goal is proved.",
    refs: "§12",
    boxes: [box(nat, vecErased), "goal Nat();"],
    initial: `-- Replace the sorry in the first line with Nat(), so that the goal
-- is proved. Change nothing else.
${taintedHole("sorry(A : Type())")}`,
    requireQed: true,
    solution: taintedHole("Nat()"),
  },
  {
    slug: "goal-comparison",
    title: "Comparing a function with a goal",
    phase: 1,
    prose: paragraphs(
      "`qed f;` checks `f`'s parameters and returns against a function goal's, position by position (§12). The comparison is between the two signatures as written. A name in them is compared by the binder it refers to, so binder names play no part, and an earlier binder's `is` clause is not in force for later ones. `is` clauses, and in phase 2 multiplicities, must agree.",
      "`subterm` marks are not compared. A mark says how `f` recurses (§9), which the goal does not state, so leaving marks out lets a recursive function prove a goal written without them.",
      "`succEq` names its binders `x` and `y` and marks `x` `subterm`, which the goal does not; neither matters. But its return is `Eq(Nat(), Succ(x), y)`, and the goal's is `Eq(Nat(), b, Succ(a))`. With `y is Succ(x)` in force the two would have the same canonical form, but the comparison does not use it, so the program is rejected at `succEq` in the `qed`, and the error names return 1, with the binders named as in the goal. Put the caret on that name: Expected shows the goal's parameters and returns."),
    task: "Make the `qed` prove the goal, by changing either the goal or `succEq`'s return.",
    refs: "§9, §12",
    boxes: [box(nat, eq)],
    initial: `-- Change the goal or succEq so that the qed proves the goal.
${succEq("Succ(x), y")}`,
    requireQed: true,
    solution: succEq("y, Succ(x)"),
  },
] };
