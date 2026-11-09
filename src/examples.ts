export const nat = `data Nat() : Type() {
  Zero() : Nat();
  Succ(pred : Nat()) : Nat();
}`;

export const vecBy = (mult: string): string => `data Vec(A : Type(), n : Nat()) : Type() {
  VNil(${mult}A : Type()) : Vec(A, Zero());
  VCons(${mult}A : Type(), ${mult}n : Nat(), head : A, rest : Vec(A, n))
    : Vec(A, Succ(n));
}`;

export const vec = vecBy("");

export const vheadBy = (mult: string): string => `fn vhead(${mult}A : Type(), ${mult}n : Nat(), v : Vec(A, Succ(n)))
    -> (x : A) {
  let VCons(_, _, hd, _) = v;
  hd
}`;
