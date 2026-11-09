export interface Term {
  term: string;
  at: string;
  means: string;
}

export const glossary: Term[] = [
  { term: "application", at: "nat", means: "A name followed by its arguments in parentheses: `Succ(Zero())`, `Nat()`. The parentheses are written even when they are empty." },
  { term: "value constructor", at: "nat", means: "One of the ways a `data` declaration gives for building a value of its type: `Zero` and `Succ` for `Nat()`." },
  { term: "branch", at: "functions", means: "One case of a `match`: a pattern for one value constructor, `=>`, and what to produce in that case." },
  { term: "scrutinee", at: "functions", means: "The value a `match` or a pattern `let` takes apart." },
  { term: "binder", at: "functions", means: "A name with its type, `n : Nat()`, or a name with what it is, `m is Succ(n)`." },
  { term: "telescope", at: "functions", means: "A parenthesized list of binders, such as a function's parameters or returns. Each binder's type can mention the names before it." },
  { term: "entry", at: "knowledge", means: "One thing the checker keeps track of. It has a type, the names that refer to it, and sometimes an `is` rule. The Scope panel lists entries." },
  { term: "`is` rule", at: "knowledge", means: "A fact the checker holds about an entry: that it is exactly some term, as `two` is `Succ(one)`." },
  { term: "canonical form", at: "knowledge", means: "What a term becomes when each entry in it is replaced by what its `is` rule says, until no rule applies. The checker compares two terms by comparing their canonical forms." },
  { term: "type constructor", at: "vhead", means: "A name that is applied to give a type: `Nat` gives `Nat()`, and `Vec` gives `Vec(Nat(), Zero())`. One declared by `data` is a data type constructor; `Type` is built in." },
  { term: "dependent type", at: "vhead", means: "A type that mentions a value, as `Vec(A, n)` mentions the length `n`." },
  { term: "forcing", at: "vhead", means: "What the checker does at a `match` or a pattern `let` for each value constructor: it supposes the scrutinee was built by that one, and records what follows." },
  { term: "refuted", at: "vhead", means: "Said of a value constructor whose forcing ends in a contradiction. The scrutinee cannot have been built by it, so it gets no branch." },
  { term: "tuple `let`", at: "vuncons", means: "`let (a, b) = e;` names the results of `e`. `let x = e;` is the same with one result." },
  { term: "pattern `let`", at: "pattern-let", means: "`let C(x, y) = e;` takes `e` apart when `C` is the only value constructor that is not refuted." },
  { term: "strict subterm", at: "termination", means: "A term strictly inside another: `k` is a strict subterm of `Succ(k)`." },
  { term: "`subterm`, `same`", at: "termination", means: "Marks on a parameter and on the arguments of a recursive call, by which the checker sees that the recursion gets smaller." },
  { term: "group", at: "termination", means: "The functions, or the `data` declarations, written together in one `mutual` block. One outside any block is a group of its own." },
  { term: "goal, `qed`", at: "equality", means: "`goal T;` states the type the program sets out to give a value of. `qed e;` offers `e` as that value." },
  { term: "`sorry`", at: "sorry", means: "A stand-in for something not written yet. It produces values of whatever types you write, with nothing behind them." },
  { term: "taint", at: "sorry", means: "The checker's record of what relies on a `sorry`. A tainted result is not evaluated and proves no goal." },
  { term: "function goal", at: "plus-zero", means: "A goal that is a function's parameters and returns. This tutorial reads it as \"for every such input there are such outputs\". `qed f;` names a function whose parameters and returns match it." },
  { term: "skeleton term", at: "plus-zero", means: "DESIGN.md's word for a term with no function call in it: names, and applications of type constructors and value constructors. Every type is one." },
  { term: "`comptime`", at: "comptime", means: "Written on a top-level pattern `let`: the right-hand side is evaluated during checking, and the run, not forcing, rules out the other value constructors." },
  { term: "phase", at: "erased", means: "Pledge's features come in phases, each adding to the one before. Phase 2 adds erasure." },
  { term: "multiplicity", at: "erased", means: "`many` or `erased`, written before a binder's name from phase 2 on. A binder is `many` unless it is written `erased`." },
  { term: "erased", at: "erased", means: "Said of a binder whose value the checker uses and evaluation skips." },
  { term: "absurd branch", at: "match-erased", means: "In an erased match, a branch whose body is a match with no branches. Evaluation runs the branch that is not absurd." },
];
