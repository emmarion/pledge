import type { Section } from "./pages.ts";
import { nat, vec } from "../examples.ts";
import { paragraphs, box, evenOdd, plusFn } from "./programs.ts";

const bool = `data Bool() : Type() {
  True() : Bool();
  False() : Bool();
}`;

const twoVec = `let one = Succ(Zero());
let xs = VCons(Nat(), one, Zero(),
  VCons(Nat(), Zero(), one, VNil(Nat())));`;

const twoThenThree = (rest: string): string => `let two = Succ(Succ(Zero()));
print two;
${rest}`;

const isZeroFn = (succBranch: string): string => `fn isZero(n : Nat()) -> (b : Bool()) {
  match n : (b : Bool()) {
    Zero() => True();${succBranch}
  }
}
print isZero(Succ(Zero()));
`;

const assertion = (comment: string, term: string): string => `let one = Succ(Zero());
let two = Succ(one);
inspect;
${comment}let y is ${term} = two;
`;

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

const vuncons = (body: string, use: string): string => `fn vuncons(A : Type(), n : Nat(), v : Vec(A, Succ(n)))
    -> (hd : A, tl : Vec(A, n)) {
  match v : (hd : A, tl : Vec(A, n)) {
    VCons(_, _, h, t) => ${body};
  }
}
${use}
`;

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

const isEvenOdd = (succBranch: string, proof: string): string => `mutual {
  fn isEven(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => True();
      Succ(m) => isOdd(subterm m);
    }
  }
  fn isOdd(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => False();${succBranch}
    }
  }
}
print isEven(Succ(Succ(Zero())));
let p : Even(Succ(Succ(Zero())))${proof};
`;

const ack = `fn ack(subterm m : Nat(), subterm n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => Succ(n);
    Succ(m1) => match n : (r : Nat()) {
      Zero() => ack(subterm m1, Succ(Zero()));
      Succ(n1) => ack(subterm m1, ack(same m, subterm n1));
    };
  }
}`;

export const basics: Section = { title: "Basics", pages: [
  {
    slug: "nat",
    title: "Data and Nat()",
    phase: 1,
    prose: paragraphs(
      "Pledge is a small language in which a type can say much more than usual: \"a list of exactly three numbers\", or even \"this number is even\". Its checker holds every program to what its types say, and this site shows you what the checker knows while it does. The tutorial builds up to that from nothing, one small task per page.",
      "Each page works the same way. The shaded boxes are given, and the last box is yours to edit. All the boxes are checked together as one program, top to bottom, as you type. The line under your box reports the result, and an error is underlined where it occurs. The panels beside the boxes (below them on a narrow screen) describe what the checker knows at the caret; the next pages introduce them one at a time.",
      "Pledge has no numbers built in, so the first box makes them. It declares a type, `Nat()`, by listing every way to build one: `Zero()`, or `Succ(n)` for a number `n` you already have. So one is `Succ(Zero())`, two is `Succ(Succ(Zero()))`, and so on. `Zero` and `Succ` are called *value constructors*: they construct the values of the type.",
      "Two things look odd at first. Parentheses are never left out, even when nothing is inside them: zero is `Zero()`, not `Zero`, and the type is `Nat()`. And every statement ends with `;`.",
      "`let two = Succ(Succ(Zero()));` gives a value a name. `print two;` evaluates `two` and shows its value beside the line, or under the box when the window is narrow."),
    task: "Bind the name `three` to the number three, and `print` it.",
    refs: "§1, §5, §8, §11, §12, §13",
    boxes: [nat],
    initial: `-- Bind the name three to the number three, and print it.
${twoThenThree("")}`,
    requireQed: false,
    solution: twoThenThree(`let three = Succ(two);
print three;
`),
  },
  {
    slug: "functions",
    title: "Functions and match",
    phase: 1,
    prose: paragraphs(
      "Most functions you will write look at a value and do something different for each way it could have been built. The function in your box asks whether a number is zero, which means asking whether it was built by `Zero` or by `Succ`.",
      "`fn isZero(n : Nat()) -> (b : Bool())` says that `isZero` takes a number `n` and returns a `Bool()`, the type the first box declares next to `Nat()`. The result has a name, `b`, just as the parameter does. The body is written between braces, and the expression at its end is what the function returns.",
      "That expression is a `match`. It looks at `n` and has one *branch* for each value constructor: a pattern such as `Zero()` or `Succ(m)`, then `=>`, then what to produce in that case. In `Succ(m)`, the name `m` stands for the number that `n` is one more than; `Succ(_)` leaves it unnamed. Patterns do not nest, so `Succ(Succ(m))` is not a pattern. Messages call the value being matched, here `n`, the *scrutinee*.",
      "After the colon, `(b : Bool())` says what the match will produce, in the same form a function uses for its returns. A name with its type, such as `b : Bool()`, is a *binder*, and a parenthesized list of binders is a *telescope*. The name seems apt because each binder in it can mention the ones before it, which starts to matter a few pages on.",
      "As it stands, the program is rejected: the match has no branch for `Succ`. Put the caret on the word `match`. The line under your box says what is missing, and the Expected panel shows what the match must produce, `b : Bool()`. Every value constructor needs a branch, apart from one the checker can rule out; a later page shows when that happens."),
    task: "Add the branch for `Succ`, so that `isZero` gives `False()` for every number built by `Succ`. The last line then prints `False()`.",
    refs: "§1, §8, §10",
    boxes: [box(nat, bool)],
    initial: `-- Add the branch for Succ, returning False().
${isZeroFn("")}`,
    requireQed: false,
    solution: isZeroFn(`
    Succ(_) => False();`),
  },
  {
    slug: "knowledge",
    title: "What the checker knows",
    phase: 1,
    prose: paragraphs(
      "From the next page on, a type can mention a value, and the checker will often have to decide whether two values are the same. For that it keeps track of what it knows about every value. This page shows you where to see that knowledge.",
      "Put the caret on the last line and look at the Scope panel. It lists `one` and `two`, each with its type and, after `is`, what it is. Each line is an *entry*: one thing the checker keeps track of, with the names that refer to it. The fact after `is` is the entry's *`is` rule*. From `let two = Succ(one);`, `two`'s rule is that it is `Succ(one)`, yet Scope shows `Succ(Succ(Zero()))`.",
      "The reason is how the checker decides that two terms are equal. It has one method. It replaces every entry by what its rule says, again and again until nothing more can be replaced, and then looks whether the two results are the same text. The result of the replacing is the term's *canonical form*, and Scope shows every rule in canonical form. No arithmetic and no cleverness is involved, which is why you can always follow it by hand.",
      "To watch it happen, put the caret on `two` in the last line. The Term panel shows the canonical form, `Succ(Succ(Zero()))`, and the two rewrites that produce it: `two` becomes `Succ(one)` by `two`'s rule, then `Succ(one)` becomes `Succ(Succ(Zero()))` by `one`'s.",
      "In the \"At the caret\" field you can type a type or an expression, and the checker answers in the scope at the caret. Type `Succ(two)`: its type is `Nat()`, and its rule is `Succ(two)`, which is `Succ(Succ(Succ(Zero())))` in canonical form.",
      "The statement `inspect;` keeps the panels of its own line in the program: where a `print` shows its value, it shows an `inspect` disclosure that you can open.",
      "The last line makes a claim for the checker to confirm: `let y is e = two;` asks whether `two` has the same canonical form as `e`, and names `two`'s entry `y` as well. One use seems to be writing down what you expect the checker to know. As written, the claim is wrong, and the error says what `two` is."),
    task: "The assertion on the last line is wrong. Fix the term after `is` so that the line checks.",
    refs: "§3, §6, §7, §8, §13",
    boxes: [nat],
    initial: assertion("-- This assertion is wrong: fix the term after is.\n", "Succ(Zero())"),
    requireQed: false,
    solution: assertion("", "Succ(Succ(Zero()))"),
  },
  {
    slug: "vhead",
    title: "Dependent types: vhead",
    phase: 1,
    prose: paragraphs(
      "Taking the first element of a list goes wrong when the list is empty. Most languages deal with that when the program runs, with an error or with a result that might be nothing. Here a type can rule it out.",
      "`Vec(A, n)` is a list that carries its length in its type: `Vec(Nat(), Succ(Succ(Zero())))` is a list of exactly two numbers. A type that mentions a value like this is called a *dependent type*, and the rest of this tutorial is about what such types can say. (`Vec` on its own is not a type; applied to an element type and a length, it gives one. Pledge calls `Vec`, and `Nat` too, a type constructor.)",
      "Look at how the box below declares the two value constructors. `VNil` builds a `Vec(A, Zero())`. `VCons` puts one more element on a `Vec(A, n)` and builds a `Vec(A, Succ(n))`. There is no other way to build a `Vec`, so the length in the type is the real length.",
      "Now `vhead` can ask for exactly what it needs: `v : Vec(A, Succ(n))`, a vector whose length is one more than some `n`. An empty vector does not fit, so a call such as `vhead(Nat(), Zero(), VNil(Nat()))` is rejected.",
      "Inside `vhead`, the `match` on `v` needs no branch for `VNil`, and the checker works that out by itself. For each value constructor it supposes that `v` was built by that one, and looks at what follows. If `v` were a `VNil`, its type would be `Vec(A, Zero())`. But its type is `Vec(A, Succ(n))`, so `Succ(n)` and `Zero()` would have to be the same value, and two different value constructors never build the same value. Pledge calls the supposing *forcing*. When forcing ends in a contradiction like this one, the value constructor is *refuted*: it gets no branch, and writing one is an error.",
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
    slug: "is-binders",
    title: "is binders",
    phase: 1,
    prose: paragraphs(
      "`cons` puts an element on the front of a vector, and returns the new length `m` together with the new vector, `w : Vec(A, m)`. The last line passes `w` to `vhead`, which wants a vector of length `Succ(Zero())`. That should work, since `w` has one element, but it is rejected.",
      "Put the caret on the last line. Scope shows `m : Nat()`, with no rule, and `w : Vec(Nat(), m)`. When the checker checks a call, it does not look into the function's body: it knows about the results only what the function's returns say, and `m : Nat()` says only that `m` is some number. One reason for working this way seems to be that a caller then depends on a function's signature alone, not on how its body happens to be written.",
      "The cure is to say more in the returns. Write `m is Succ(n)` in place of `m : Nat()`. A return written this way is a promise the function makes about its result: `m` will be exactly `Succ(n)`, for whatever `n` the caller passes. Its type is the type of `Succ(n)`, `Nat()`. It is the same `is` as in the assertion on the page \"What the checker knows\".",
      "Both sides are held to the promise. When the body is checked, its first result must have the same canonical form as `Succ(n)`; promise `Succ(Succ(n))` instead and the body is rejected. At every call, the result gets the promise as its `is` rule. After the fix, Scope on the last line shows `m : Nat() is Succ(Zero())` and `w : Vec(Nat(), Succ(Zero()))`, which is what `vhead` wants."),
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
      "`vsecond` takes a vector of at least two elements, `Vec(A, Succ(Succ(n)))`, and its pattern `let` takes off the first one. Put the caret on `rest` in the line after it: Scope shows `rest : Vec(A, Succ(n))`, a vector of at least one element. So a second pattern `let` can take the next element off `rest`. As it stands, the function returns `rest` itself where an element is expected, and the error says so.",
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
  {
    slug: "termination",
    title: "Termination: subterm and same",
    phase: 1,
    prose: paragraphs(
      "Later pages read a type as a claim and a value of it as a proof, and for that every function must return. A function `fn f(n : Nat()) -> (r : T)` whose body is `f(n)` would never return, yet its body has type `T`, whatever `T` is. This tutorial's account is that such a function could \"prove\" any claim; the page \"Why Pledge appears sound\" comes back to this.",
      "So Pledge lets a function call any function declared before it, but call itself only on something smaller, and you mark what gets smaller. Mark a parameter *`subterm`*, as in `fn plus(subterm m : Nat(), n : Nat())`, and mark the matching argument of the call to itself the same way, as in `plus(subterm k, n)`. The marks are always written; the checker never guesses them.",
      "The checker then requires the marked argument to be a *strict subterm* of the marked parameter: a term strictly inside it, as `k` is inside `Succ(k)`. Put the caret on the call to `plus` in the `Succ(k)` branch: Scope shows `m : Nat() is Succ(k)`, so `k` is a strict subterm of `m`. One reason this seems to be enough is that a value is built in finitely many steps, so it can be taken apart only finitely many times.",
      "A function can mark several parameters `subterm`, as `ack` in the first box does. In `ack(same m, subterm n1)`, the second argument gets smaller while the first is the caller's own `m`, unchanged, marked *`same`*. In general, a call marks one argument `subterm`, marks `same` the arguments for the `subterm` parameters before that one, and leaves the rest unmarked, as `Succ(Zero())` is in `ack(subterm m1, Succ(Zero()))`.",
      "The error on `plus` says that the call is within `plus`'s group. A *group* is the functions written together in a `mutual` block, the subject of the next page; a function outside any block, like `plus`, is a group of its own. The Termination panel shows the function at the caret, its `subterm` parameters, and its group."),
    task: "`plus` is rejected as it stands. Add the marks that let it call itself, so that the last line prints six, `Succ` applied six times to `Zero()`.",
    refs: "§8, §9, §13",
    boxes: [box(nat, ack)],
    initial: `-- Mark the recursion so that plus is accepted.
${plusFn("")}
let two = Succ(Succ(Zero()));
print plus(two, ack(Succ(Zero()), two));
`,
    requireQed: false,
    solution: `${plusFn("subterm ")}
let two = Succ(Succ(Zero()));
print plus(two, ack(Succ(Zero()), two));
`,
  },
  {
    slug: "mutual",
    title: "Mutual groups: Even and Odd",
    phase: 1,
    prose: paragraphs(
      "Some things are defined in terms of each other. A number is even when it is zero or one more than an odd number, and odd when it is one more than an even number. Neither definition can come first, since each mentions the other. In Pledge you write such declarations together in a `mutual` block, and they form one group.",
      "The first box declares `Even(n)` and `Odd(n)` this way. A value of type `Even(n)` can be read as evidence that `n` is even, because the only ways to build one follow the definition: `EvenZero()` is evidence that zero is even, and `EvenSucc(n, p)` turns evidence `p` that `n` is odd into evidence that `Succ(n)` is even.",
      "Functions can be mutual too, and your box declares `isEven` and `isOdd` in one block. A `mutual` block holds either `data` declarations or functions, not both. Functions of one group call each other under the rule of the last page, as a function calls itself: `isOdd(subterm m)` marks the argument that gets smaller, for `isOdd`'s `subterm` parameter. Put the caret inside `isOdd`: the Termination panel lists its group, `isEven, isOdd`.",
      "The last line, `let p : Even(Succ(Succ(Zero()))) = EvenZero();`, asks the checker to confirm a type, as `is` asked it to confirm a value on the page \"What the checker knows\": the type after the colon must have the same canonical form as the type of the right-hand side. `EvenZero()` has type `Even(Zero())`, so once `isOdd` is complete, that line is the error."),
    task: "Give `isOdd` its `Succ` branch, calling `isEven`. Then replace `EvenZero()` with evidence that two is even, a value of type `Even(Succ(Succ(Zero())))`.",
    refs: "§5, §6, §8, §9, §13",
    boxes: [box(nat, bool, evenOdd)],
    initial: `-- Give isOdd a Succ branch calling isEven, then replace EvenZero()
-- with evidence that two is even.
${isEvenOdd("", " = EvenZero()")}`,
    requireQed: false,
    solution: isEvenOdd(`
      Succ(m) => isEven(subterm m);`, `
  = EvenSucc(Succ(Zero()), OddSucc(Zero(), EvenZero()))`),
  },
] };
