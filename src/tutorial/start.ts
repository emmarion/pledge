import type { Section } from "./pages.ts";
import { nat, vec, vheadBy } from "../examples.ts";
import { paragraphs, box, bool } from "./programs.ts";

const lists = `let list = VCons(Nat(), Zero(), Succ(Zero()), VNil(Nat()));
let empty = VNil(Nat());`;

const firstOf = (second: string): string => `print vhead(Nat(), Zero(), list);
print vhead(Nat(), Zero(), ${second});
`;

const twoThenThree = (rest: string): string => `let two = Succ(Succ(Zero()));
print two;
${rest}`;

const isZeroFn = (succBranch: string): string => `fn isZero(n : Nat()) -> (b : Bool()) {
  match n : (b : Bool()) {
    Zero() => Yes();${succBranch}
  }
}
print isZero(Succ(Zero()));
`;

const assertion = (comment: string, term: string): string => `let one = Succ(Zero());
let two = Succ(one);
inspect;
${comment}let y is ${term} = two;
`;

export const start: Section = { title: "First steps", pages: [
  {
    slug: "first-look",
    title: "A first look",
    phase: 1,
    prose: paragraphs(
      "Pledge is a small language in which a type can say much more than usual: \"a list of exactly three numbers\", or even \"this number is even\". Its checker holds every program to what its types say. The tutorial builds up to that, one small task per page, and assumes only that you have programmed before, in any language.",
      "This page is a preview. The shaded boxes are given, and the last box is yours to edit. Do not try to read the shaded ones yet; take one thing from them: `vhead` returns the first element of a list, and its type says that the list must have at least one element.",
      "Your box calls `vhead` twice: on `list`, which holds one number, and on `empty`, which holds none. The first line prints `Succ(Zero())`, Pledge's way of writing one. In most languages the second call would be accepted too, and would go wrong when the program ran. Here it never runs: the checker rejects it as you type, underlines `empty`, and says why under your box.",
      "Read the two types in the message. `Vec(Nat(), Succ(Zero()))` is a list of exactly one number, which the call needs, and `Vec(Nat(), Zero())` is a list of none, which it got. The length of a list is part of its type, so a list of the wrong length is a type error, like text where a number belongs. The rest of the tutorial builds on this: types that mention values rule out mistakes before a program runs, and later they state facts, which programs prove."),
    task: "Read the message under your box. Then change `empty` to `list` in the last line, so that the program is accepted and both lines print.",
    refs: "§3, §8",
    boxes: [box(nat, vec, vheadBy("")), lists],
    initial: `-- The last line is rejected. Read the message, then fix the line.
${firstOf("empty")}`,
    requireQed: false,
    solution: firstOf("list"),
  },
  {
    slug: "nat",
    title: "Data and Nat()",
    phase: 1,
    prose: paragraphs(
      "Each page works the way the first one did. All the boxes are checked together as one program, top to bottom, as you type. The line under your box reports the result, and an error is underlined where it occurs. The panels beside the boxes (below them on a narrow screen) show what the checker knows at the caret, the text cursor; the next pages introduce them one at a time.",
      "The first page used numbers and lists without saying where they come from. Pledge has neither built in, so the first box makes numbers. It is a `data` declaration: it declares a type, `Nat()`, by listing every way to build one: `Zero()`, or `Succ(n)` for a number `n` you already have. So one is `Succ(Zero())`, two is `Succ(Succ(Zero()))`, and so on. `Zero` and `Succ` are called *value constructors*: they construct the values of the type. Read the line `Succ(pred : Nat()) : Nat();` as: `Succ` takes one `Nat()`, which the declaration calls `pred`, and builds a `Nat()`. The `: Type()` in the first line says that `Nat()` is a type.",
      "Two things look odd at first. Parentheses are never left out, even when nothing is inside them: zero is `Zero()`, not `Zero`, and the type is `Nat()`. And every statement ends with `;`. A line that starts with `--` is a comment.",
      "Pledge is explicit on purpose. Its programs spell out what other languages would work out silently, so that everything the checker uses is on the page and you can follow each of its steps by hand. Some lines get long that way. Later pages introduce `_` for the parts that are obvious.",
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
    revision: 2,
    title: "Functions and match",
    phase: 1,
    prose: paragraphs(
      "Most functions you will write look at a value and do something different for each way it could have been built. The function in your box asks whether a number is zero, which means asking whether it was built by `Zero` or by `Succ`.",
      "`fn isZero(n : Nat()) -> (b : Bool())` says that `isZero` takes a number `n` and returns a `Bool()`, the type the first box declares next to `Nat()`, with two values, `Yes()` and `No()`. The result has a name, `b`, just as the parameter does. The body is written between braces, and the expression at its end is what the function returns.",
      "That expression is a `match`. It looks at `n` and has one *branch* for each value constructor: a pattern such as `Zero()` or `Succ(m)`, then `=>`, then what to produce in that case. In `Succ(m)`, the name `m` stands for the number that `n` is one more than; `Succ(_)` leaves it unnamed. Patterns do not nest, so `Succ(Succ(m))` is not a pattern. Messages call the value being matched, here `n`, the *scrutinee*.",
      "After the colon, `(b : Bool())` says what the match will produce, in the same form a function uses for its returns. A name with its type, such as `b : Bool()`, is a *binder*, and a parenthesized list of binders is a *telescope*. The name fits because each binder in it can mention the ones before it, which starts to matter a few pages on.",
      "If you know Java 21, you have seen this shape. A `data` declaration corresponds closely to a sealed interface with one record for each value constructor, and a `match` to a `switch` over it with no `default`, which the compiler rejects when a case is missing. Rust's `enum` and `match`, Swift's `enum` and `switch`, and Kotlin's sealed classes and `when` are close relatives.",
      "As it stands, the program is rejected: the match has no branch for `Succ`. Put the caret on the word `match`. The line under your box says what is missing, and the Expected panel shows what the match must produce, `b : Bool()`. Every value constructor needs a branch, apart from one the checker can rule out; a later page shows when that happens."),
    task: "Add the branch for `Succ`, so that `isZero` gives `No()` for every number built by `Succ`. The last line then prints `No()`.",
    refs: "§1, §8, §10",
    boxes: [box(nat, bool)],
    initial: `-- Add the branch for Succ, returning No().
${isZeroFn("")}`,
    requireQed: false,
    solution: isZeroFn(`
    Succ(_) => No();`),
  },
  {
    slug: "knowledge",
    title: "What the checker knows",
    phase: 1,
    prose: paragraphs(
      "From the next page on, a type can mention a value, and the checker will often have to decide whether two values are the same. For that it keeps track of what it knows about every value. This page shows you where to see that knowledge.",
      "Put the caret on the last line and look at Local entries. Outside any function every entry is global, so Local entries points you to Global entries, just below it: open it. It lists `one` and `two`, each with its type and, after `is`, what it is, and a line beginning `?@` for the `Zero()` inside `one`, which has no name. Each line is an *entry*: one thing the checker keeps track of, with the names that refer to it. The fact after `is` is the entry's *`is` rule*. From `let two = Succ(one);`, `two`'s rule is that it is `Succ(one)`, yet Global entries shows `Succ(Succ(Zero()))`.",
      "The reason is how the checker decides that two terms are equal. It has one method. It replaces every entry by what its rule says, again and again until nothing more can be replaced, and then looks whether the two results are the same text. The result of the replacing is the term's *canonical form*, and the panels show every rule in canonical form. The `steps` link beside `two`'s rule shows the rule as written, `Succ(one)`, and the rewrite that reaches the canonical form. No arithmetic and no cleverness is involved, which is why you can always follow it by hand. Other languages with types like these run functions while they compare types. Pledge's checker never does, and the section \"Addition as a relation\" shows what you write instead.",
      "To watch it happen, put the caret on `two` in the last line. The Term panel shows the canonical form, `Succ(Succ(Zero()))`, and the two rewrites that produce it: `two` becomes `Succ(one)` by `two`'s rule, then `Succ(one)` becomes `Succ(Succ(Zero()))` by `one`'s.",
      "In the \"At the caret\" field you can type a type or an expression, and the checker answers in the scope at the caret. Type `Succ(two)`: its type is `Nat()`, and its rule is `Succ(two)`, which is `Succ(Succ(Succ(Zero())))` in canonical form.",
      "The statement `inspect;` keeps the panels of its own line in the program: where a `print` shows its value, it shows an `inspect` disclosure that you can open.",
      "The last line makes a claim for the checker to confirm: `let y is e = two;` asks whether `two` has the same canonical form as `e`, and names `two`'s entry `y` as well. It is a way to write down what you expect the checker to know. As written, the claim is wrong, and the error says what `two` is."),
    task: "The assertion on the last line is wrong. Fix the term after `is` so that the line checks.",
    refs: "§3, §6, §7, §8, §13",
    boxes: [nat],
    initial: assertion("-- This assertion is wrong: fix the term after is.\n", "Succ(Zero())"),
    requireQed: false,
    solution: assertion("", "Succ(Succ(Zero()))"),
  },
] };
