import { vecBy, vheadBy } from "../examples.ts";

export const paragraphs = (...ps: string[]): string => ps.join("\n\n");

export const box = (...parts: string[]): string => parts.join("\n\n");

export const evenOdd = `mutual {
  data Even(n : Nat()) : Type() {
    EvenZero() : Even(Zero());
    EvenSucc(n : Nat(), p : Odd(n)) : Even(Succ(n));
  }
  data Odd(n : Nat()) : Type() {
    OddSucc(n : Nat(), p : Even(n)) : Odd(Succ(n));
  }
}`;

export const plusFn = (mark: string): string => `fn plus(${mark}m : Nat(), n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => n;
    Succ(k) => Succ(plus(${mark}k, n));
  }
}`;

export const plusRel = `data Plus(m : Nat(), n : Nat(), r : Nat()) : Type() {
  PlusZero(n : Nat()) : Plus(Zero(), n, n);
  PlusSucc(m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    : Plus(Succ(m), n, Succ(r));
}`;

export const plusEvidence = `fn plus(subterm m : Nat(), n : Nat())
    -> (r : Nat(), p : Plus(m, n, r)) {
  match m : _ {
    Zero() => (n, PlusZero(n));
    Succ(k) => {
      let (r, p) = plus(subterm k, n);
      (Succ(r), PlusSucc(k, n, r, p))
    };
  }
}`;

export const plus = box(plusRel, plusEvidence);

export const eq = `data Eq(A : Type(), x : A, y : A) : Type() {
  Refl(A : Type(), x : A) : Eq(A, x, x);
}`;

export const isZero = `data IsZero(n : Nat()) : Type() {
  IsZeroHere() : IsZero(Zero());
}`;

export const vecErased = vecBy("erased ");

export const vheadErased = vheadBy("erased ");

export const bool = `data Bool() : Type() {
  Yes() : Bool();
  No() : Bool();
}`;

export const twoVec = `let one = Succ(Zero());
let xs = VCons(Nat(), one, Zero(),
  VCons(Nat(), Zero(), one, VNil(Nat())));`;

export const vuncons = (body: string, use: string, ann = "(hd : A, tl : Vec(A, n))"): string =>
  `fn vuncons(A : Type(), n : Nat(), v : Vec(A, Succ(n)))
    -> (hd : A, tl : Vec(A, n)) {
  match v : ${ann} {
    VCons(_, _, h, t) => ${body};
  }
}
${use}
`;

export const falseType = `data False() : Type() {}`;

export const gap = " sorry(_)";

export const withQed = (fn: string, name: string): string => `${fn}
qed ${name};
`;
