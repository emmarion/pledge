import type { Section } from "./pages.ts";
import { nat, vec } from "../examples.ts";
import { paragraphs, box, twoVec, vuncons } from "./programs.ts";

const vheadWith = (branch: string): string => `fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  match v : (x : A) {${branch}
  }
}`;

const vhead = vheadWith(`
    VCons(_, _, hd, _) => hd;`);

const vheadUse = (fn: string): string => `${fn}
let v = VCons(Nat(), Zero(), Succ(Zero()), VNil(Nat()));
print vhead(Nat(), Zero(), v);
`;

const tailHead = (type: string): string => `let (h, t) = vuncons(Nat(), one, xs);
let y${type} = match t : _ {
  VCons(_, _, z, _) => z;
};
print y;`;

const cons = (m: string): string => `fn cons(A : Type(), n : Nat(), x : A, v : Vec(A, n))
    -> (${m}, w : Vec(A, m)) {
  (Succ(n), VCons(A, n, x, v))
}
let (m, w) = cons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), w);
`;

const vsecond = (rest: string): string => `fn vsecond(A : Type(), n : Nat(), v : Vec(A, Succ(Succ(n))))
    -> (x : A) {
  let VCons(_, _, _, rest) = v;
  ${rest}
}
print vsecond(Nat(), Zero(), xs);
`;

export const dependent: Section = { title: "Types that mention values", pages: [
  {
    slug: "vhead",
    title: "Dependent types: vhead",
    phase: 1,
    prose: paragraphs(
      "Taking the first element of a list goes wrong when the list is empty. Most languages deal with that when the program runs, with an error or with a result that might be nothing. In Java, `list.getFirst()` throws a `NoSuchElementException`, and `stream.findFirst()` returns an `Optional` that every caller has to unwrap. On the first page, the checker turned such a call away before anything ran. This page shows how, and you write `vhead` yourself.",
      "`Vec(A, n)` is a list that carries its length in its type: `Vec(Nat(), Succ(Succ(Zero())))` is a list of exactly two numbers. A type that mentions a value like this is called a *dependent type*, and the rest of this tutorial is about what such types can say. (`Vec` on its own is not a type; applied to an element type and a length, it gives one. Pledge calls `Vec`, and `Nat` too, a type constructor.)",
      "Look at how the box below declares the two value constructors. `VNil` builds a `Vec(A, Zero())`. `VCons` puts one more element on a `Vec(A, n)` and builds a `Vec(A, Succ(n))`. There is no other way to build a `Vec`, so the length in the type is the real length.",
      "Now `vhead` can ask for exactly what it needs: `v : Vec(A, Succ(n))`, a vector whose length is one more than some `n`. An empty vector does not fit, so a call such as `vhead(Nat(), Zero(), VNil(Nat()))` is rejected. `vhead` needs neither an exception nor an `Optional`: the empty case never reaches it.",
      "A call names the element type and `n` as well as the vector. Other languages would work those two out. Here you write them, and see exactly what `vhead` is given. The section \"Erasure\" lets you write `_` for arguments like these.",
      "Inside `vhead`, the `match` on `v` needs no branch for `VNil`, and the checker works that out by itself. For each value constructor it supposes that `v` was built by that one, and looks at what follows. If `v` were a `VNil`, its type would be `Vec(A, Zero())`. But its type is `Vec(A, Succ(n))`, so `Succ(n)` and `Zero()` would have to be the same value, and two different value constructors never build the same value. Pledge calls the supposing *forcing*. When forcing ends in a contradiction like this one, the value constructor is *refuted*: it gets no branch, and writing one is an error. In the terms of an exhaustive `switch`, a refuted value constructor is a case the compiler has proved cannot happen.",
      "One detail in the declarations: `VNil` and `VCons` each take an `A` of their own, because the names in `Vec(A : Type(), n : Nat())` belong to that line only."),
    task: "Give the match its one branch, so that the last line prints `Succ(Zero())`. Then put the caret on the word `match` and open `VNil` in the Refutations panel: it lists the steps that lead to the contradiction.",
    refs: "§3, §5, §7, §10, §13",
    boxes: [box(nat, vec)],
    initial: `-- Give the match its one branch, the one for VCons.
${vheadUse(vheadWith(""))}`,
    requireQed: false,
    solution: vheadUse(vhead),
  },
  {
    slug: "vuncons",
    title: "Several results",
    phase: 1,
    prose: paragraphs(
      "Taking a vector apart gives two things: its first element and the rest. A function that could return only one of them would make you take the vector apart twice. In Pledge a function can return several values at once.",
      "`vuncons` has two returns, `hd : A` and `tl : Vec(A, n)`; the type of the tail says that it is one element shorter. Its `match` produces the same two, so the match's telescope lists both. A branch must then produce two values, and you write them as a tuple, `(h, t)`, one value per element, in order.",
      "Put the caret on the branch body, the `h` after `=>`. Expected lists two entries, `hd : A` and `tl : Vec(A, n)`, and the error says that 2 values are expected there and the body produces 1. Once the body is a tuple, put the caret on its `h`, then on its `t`: Expected shows `hd : A` for the first and `tl : Vec(A, n)` for the second, since each element of a tuple is given one entry.",
      "A call to `vuncons` produces two values too, so `let h = vuncons(Nat(), one, xs);` is rejected the other way round: 1 value is expected and the call produces 2. `let (h, t) = vuncons(Nat(), one, xs);` names both results. This form is a *tuple `let`*, and the `let x = e;` you have used so far is a tuple `let` with one name and the parentheses left out."),
    task: "Make the branch produce both the head and the tail. Then bind both results of the call with a tuple `let`, and `print` both.",
    refs: "§8, §10, §13",
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return both the head and the tail, then bind and print both.
${vuncons("h", `let h = vuncons(Nat(), one, xs);
print h;`)}`,
    requireQed: false,
    solution: vuncons("(h, t)", `let (h, t) = vuncons(Nat(), one, xs);
print h;
print t;`),
  },
  {
    slug: "annotation-underscore",
    title: "_ for match annotations",
    phase: 1,
    prose: paragraphs(
      "A match's annotation often repeats what the code around it already says. In `vuncons`, the match is the whole body, so it produces the function's returns, and its annotation writes `(hd : A, tl : Vec(A, n))` out a second time.",
      "You can write `_` in its place: `match v : _`. The `_` stands for the whole telescope given at its position, here the function's returns. Hover over the `_`, or put the caret on it: the tip, and the Term panel under \"Stands for\", show `hd : A` and `tl : Vec(A, n)`.",
      "A `_` like this needs a whole telescope to be given at its position. A function body is given one, and so is a branch body, the right-hand side of a tuple `let` whose binders all carry a type or an `is` clause, and the final expression of a block at one of these. A `_` never stands for a single entry, so an argument or an element of a tuple is not such a place.",
      "Nor is the `let` at the end of your box. Its binder `y` has neither a type nor an `is` clause, so it takes whatever the match produces, and nothing is given for the `_` to stand for. The program is rejected at that `_`, and the error says that none is given here. Write `let y : Nat()` instead, and the `_` stands for `y : Nat()`. A type written on a `let` is also a check: the right-hand side must produce a value of that type."),
    task: "Replace the annotation of the match in `vuncons` with `_`, and hover over it. Then give `y` a type, so that the program checks and the last line prints `Succ(Zero())`.",
    refs: "§8, §10, §13",
    boxes: [box(nat, vec), twoVec],
    initial: `-- Replace the match's annotation with _, then give y a type.
${vuncons("(h, t)", tailHead(""))}`,
    requireQed: false,
    solution: vuncons("(h, t)", tailHead(" : Nat()"), "_"),
  },
  {
    slug: "is-binders",
    title: "is binders",
    phase: 1,
    prose: paragraphs(
      "`cons` puts an element on the front of a vector, and returns the new length `m` together with the new vector, `w : Vec(A, m)`. The last line passes `w` to `vhead`, which wants a vector of length `Succ(Zero())`. That should work, since `w` has one element, but it is rejected.",
      "Put the caret on the last line. Global entries shows `m : Nat()`, with no rule, and `w : Vec(Nat(), m)`. When the checker checks a call, it does not look into the function's body: it knows about the results only what the function's returns say, and `m : Nat()` says only that `m` is some number. A caller then depends on a function's signature alone, not on how its body happens to be written. That is a rule of the language, not a gap in the checker, and the section \"Addition as a relation\" shows how much a function's returns can say.",
      "The cure is to say more in the returns. Write `m is Succ(n)` in place of `m : Nat()`. A return written this way is a promise the function makes about its result: `m` will be exactly `Succ(n)`, for whatever `n` the caller passes. Its type is the type of `Succ(n)`, `Nat()`. It is the same `is` as in the assertion on the page \"What the checker knows\".",
      "Both sides are held to the promise. When the body is checked, its first result must have the same canonical form as `Succ(n)`; promise `Succ(Succ(n))` instead and the body is rejected. At every call, the result gets the promise as its `is` rule. After the fix, Global entries on the last line shows `m : Nat() is Succ(Zero())` and `w : Vec(Nat(), Succ(Zero()))`, which is what `vhead` wants."),
    task: "Change `m`'s binder in `cons`'s returns to an `is` binder, so that the last line checks and prints `Zero()`.",
    refs: "§6, §7, §8",
    boxes: [box(nat, vec, vhead)],
    initial: `-- Change m : Nat() to an is binder, so that the last line checks.
${cons("m : Nat()")}`,
    requireQed: false,
    solution: cons("m is Succ(n)"),
  },
  {
    slug: "pattern-let",
    title: "Pattern let",
    phase: 1,
    prose: paragraphs(
      "In `vhead`, the match on `v` has a single branch, because `VNil` is refuted. That is a lot of ceremony for \"take `v` apart\": a telescope, a pattern, an arrow, and the rest of the function inside the branch.",
      "`let VCons(_, _, h, t) = v;` says the same in one line. It is a *pattern `let`*: it takes `v` apart, names its fields (a `_` leaves one unnamed), and the code after it goes on in the same block. At the `let`, the Refutations panel lists `VNil`, as it would at a `match`.",
      "It works only when the checker can rule out every value constructor but the one you wrote: after forcing, exactly one value constructor must be left that is not refuted, and it must be yours. With `n : Nat()` and nothing more known, `let Succ(k) = n;` is rejected, since `n` could be `Zero()`.",
      "`vsecond` takes a vector of at least two elements, `Vec(A, Succ(Succ(n)))`, and its pattern `let` takes off the first one. Put the caret on `rest` in the line after it: Local entries shows `rest : Vec(A, Succ(n))`, a vector of at least one element. So a second pattern `let` can take the next element off `rest`. As it stands, the function returns `rest` itself where an element is expected, and the error says so.",
      "The names a pattern `let` introduces last to the end of its block. What it taught the checker can last longer, as the appendix page \"Facts outlive names\" shows."),
    task: "Finish `vsecond`: take `rest` apart with a second pattern `let`, and return its first element. The last line then prints `Succ(Zero())`.",
    refs: "§7, §8, §10, §13",
    boxes: [box(nat, vec), twoVec],
    initial: `-- Return v's second element, with a second pattern let on rest.
${vsecond("rest")}`,
    requireQed: false,
    solution: vsecond(`let VCons(_, _, y, _) = rest;
  y`),
  },
] };
