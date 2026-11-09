import type { Phase } from "../syntax.ts";

export interface Page {
  slug: string;
  title: string;
  phase: Phase;
  prose: string;
  boxes: string[];
  initial: string;
  requireQed: boolean;
}

const nat = `data Nat() : Type() {
  Zero() : Nat();
  Succ(pred : Nat()) : Nat();
}`;

const vec = `data Vec(A : Type(), n : Nat()) : Type() {
  VNil(A : Type()) : Vec(A, Zero());
  VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));
}`;

const isZero = `data IsZero(n : Nat()) : Type() {
  IsZeroHere() : IsZero(Zero());
}`;

export const pages: Page[] = [
  {
    slug: "nat",
    title: "Natural numbers",
    phase: 1,
    prose: "A placeholder page. The box above declares `Nat`. Below it, build a number and `print` it.",
    boxes: [nat],
    initial: "let two = Succ(Succ(Zero()));\nprint two;\n",
    requireQed: false,
  },
  {
    slug: "vectors",
    title: "Vectors",
    phase: 1,
    prose: "A placeholder page. `Vec(A, n)` is a list of `n` values of type `A`. Put the caret inside `vhead` to see what the checker knows there.",
    boxes: [nat, vec],
    initial: "fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {\n  let VCons(_, _, hd, _) = v;\n  hd\n}\n",
    requireQed: false,
  },
  {
    slug: "first-goal",
    title: "A first goal",
    phase: 1,
    prose: "A placeholder page. The goal is `IsZero(Zero())`. Write a `qed` statement in your box that proves it.",
    boxes: [nat, isZero, "goal IsZero(Zero());"],
    initial: "-- Write the qed statement here.\n",
    requireQed: true,
  },
];
