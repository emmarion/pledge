import type { Section } from "./pages.ts";
import { nat, vec } from "../examples.ts";
import { paragraphs, box, bool, plusFn, twoVec } from "./programs.ts";

const ack = `fn ack(subterm m : Nat(), subterm n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => Succ(n);
    Succ(m1) => match n : (r : Nat()) {
      Zero() => ack(subterm m1, Succ(Zero()));
      Succ(n1) => ack(subterm m1, ack(same m, subterm n1));
    };
  }
}`;

const isEvenOdd = (succBranch: string): string => `mutual {
  fn isEven(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => Yes();
      Succ(m) => isOdd(subterm m);
    }
  }
  fn isOdd(subterm n : Nat()) -> (b : Bool()) {
    match n : (b : Bool()) {
      Zero() => No();${succBranch}
    }
  }
}
let two = Succ(Succ(Zero()));
print isEven(two);
print isOdd(two);
`;

const pair = `data Pair(A : Type(), B : Type()) : Type() {
  MkPair(A : Type(), B : Type(), fst : A, snd : B) : Pair(A, B);
}`;

const vzip = (tail: string): string => `fn vzip(A : Type(), B : Type(), n : Nat(), subterm v : Vec(A, n),
    w : Vec(B, n)) -> (r : Vec(Pair(A, B), n)) {
  match v : (r : Vec(Pair(A, B), n)) {
    VNil(_) => VNil(Pair(A, B));
    VCons(_, k, x, vs) => {
      let VCons(_, _, y, ws) = w;
      VCons(Pair(A, B), k, MkPair(A, B, x, y),
        ${tail})
    };
  }
}
print vzip(Nat(), Nat(), Succ(one), xs, xs);
`;

export const recursion: Section = { title: "Recursion", pages: [
  {
    slug: "termination",
    title: "Termination: subterm and same",
    phase: 1,
    prose: paragraphs(
      "In most languages, a function that calls itself forever is just a bug. In Pledge it would do more damage. Later pages read a type as a claim and a value of that type as a proof. A function `fn f(n : Nat()) -> (r : T)` whose body is `f(n)` never returns, yet its body has type `T`, whatever `T` is, so it would \"prove\" any claim. The page \"Soundness\" comes back to this.",
      "So Pledge lets a function call any function declared before it, but call itself only on something smaller, and you mark what gets smaller. Mark a parameter *`subterm`*, as in `fn plus(subterm m : Nat(), n : Nat())`, and mark the matching argument of the call to itself the same way, as in `plus(subterm k, n)`. The marks are always written; the checker never guesses them.",
      "The checker then requires the marked argument to be a *strict subterm* of the marked parameter: a term strictly inside it, as `k` is inside `Succ(k)`. Put the caret on the call to `plus` in the `Succ(k)` branch: Scope shows `m : Nat() is Succ(k)`, so `k` is a strict subterm of `m`. This is enough because a value is built in finitely many steps, so it can be taken apart only finitely many times.",
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
    revision: 2,
    title: "Mutual groups",
    phase: 1,
    prose: paragraphs(
      "Some things are defined in terms of each other. A number is even when it is zero or one more than an odd number, and odd when it is one more than an even number. Neither definition can come first, since each mentions the other. In Pledge you write such declarations together in a `mutual` block, and they form one group.",
      "Your box does this for two functions. `isEven` asks whether a number is even, and for `Succ(m)` it passes the question on to `isOdd`, which passes it back. Written one after the other, they would be rejected: a name is in scope only after its declaration, so the first of the two could not call the second. Inside a `mutual` block, each can call the other.",
      "Functions of one group call each other under the rule of the previous page, as a function calls itself. `isOdd(subterm m)` marks the argument that gets smaller, and the checker requires `m` to be a strict subterm of `isEven`'s own `subterm` parameter. So the two can hand a number back and forth only while it shrinks, and every call returns. Put the caret inside `isOdd`: the Termination panel lists its group, `isEven, isOdd`.",
      "A `mutual` block can hold `data` declarations in place of functions, for types defined in terms of each other, though not both kinds at once. The page \"Evidence: Even and Odd\" has one."),
    task: "Give `isOdd` its `Succ` branch, calling `isEven`. The last two lines then print `Yes()` and `No()`.",
    refs: "§2, §8, §9, §13",
    boxes: [box(nat, bool)],
    initial: `-- Give isOdd a Succ branch calling isEven.
${isEvenOdd("")}`,
    requireQed: false,
    solution: isEvenOdd(`
      Succ(m) => isEven(subterm m);`),
  },
  {
    slug: "vzip",
    title: "Recursion on a vector: vzip",
    phase: 1,
    prose: paragraphs(
      "Recursion and dependent types work well together. `vzip` pairs up two vectors: the first elements together, the second elements together, and so on. In most languages a zip has to decide what happens when one list is longer than the other: stop early, or fail when the program runs. Here the question cannot come up. Both parameters, `v : Vec(A, n)` and `w : Vec(B, n)`, use the same `n`, so a call with vectors of different lengths is rejected, as an empty vector was for `vhead`.",
      "`Pair(A, B)`, in the first box, is a type for two values kept together, and `MkPair(A, B, x, y)` builds one. The result of `vzip` is a `Vec(Pair(A, B), n)`: as many pairs as each vector has elements.",
      "The function is a recursion on `v`, which is marked `subterm`, and its `match` shows what the shared `n` buys inside the body. Put the caret in the `VNil` branch, on `VNil(Pair(A, B))`. Scope shows that `n` is `Zero()`, so `w : Vec(B, Zero())`, and Expected asks for `r : Vec(Pair(A, B), Zero())`: the empty vector of pairs. Nothing has to be done about `w`.",
      "The body of the `VCons` branch is a block: statements between braces, ending in the expression that the branch produces. Put the caret on its first statement, the pattern `let`. Forcing `VCons` on `v` told the checker that `n` is `Succ(k)`, so Scope shows `w : Vec(B, Succ(k))`. The checker never looked at `w`, but it knows that `w` is not empty, because `w` has the length of `v`. So the pattern `let` on `w` is accepted, and Refutations lists `VNil` there. There is no case for \"`v` has an element and `w` has none\" to write, and none to forget.",
      "The branch then builds the result: the pair of the two heads, in front of the zip of the two tails. As it stands, it puts the tail `ws` where the zipped tails belong, and the error says that a `Vec(Pair(A, B), k)` is needed there. That calls for `vzip` itself, on `vs` and `ws`. The call is within `vzip`'s group, so it marks the argument that gets smaller: `vs` is a strict subterm of `v`, since Scope shows that `v` is `VCons(A, k, x, vs)`."),
    task: "Replace `ws` at the end of the `VCons` branch with a call to `vzip` on the two tails, so that the last line prints two pairs. Then add `print vzip(Nat(), Nat(), Succ(one), xs, VNil(Nat()));` at the end of your box, read the error, and delete the line.",
    refs: "§7, §8, §9, §10, §13",
    boxes: [box(nat, vec, pair), twoVec],
    initial: `-- Replace ws with a call to vzip on the two tails.
${vzip("ws")}`,
    requireQed: false,
    solution: vzip("vzip(A, B, k, subterm vs, ws)"),
  },
] };
