# Pledge

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24092650.svg)](https://doi.org/10.5281/zenodo.24092650)

Pledge is a small language for learning restricted dependent types,
built so that you can see what its type checker knows at every point of
a program. It runs entirely in the browser:

- **[Try it](https://emmarion.github.io/pledge/)**: an editor with the
  checker's view beside it.
- **[Take the tutorial](https://emmarion.github.io/pledge/tutorial.html)**:
  pages that each set a task, from `Nat` to proofs about addition and
  multiplication.

```
data Nat() : Type() {
  Zero() : Nat();
  Succ(pred : Nat()) : Nat();
}

data Vec(A : Type(), n : Nat()) : Type() {
  VNil(A : Type()) : Vec(A, Zero());
  VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));
}

fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  let VCons(_, _, hd, _) = v;
  hd
}
```

`vhead` takes only a vector whose length is `Succ(n)`, so it has no case
for the empty vector: the checker works out that `VNil` cannot be the
value constructor of `v`, and the page shows the reasoning.

## What you see

Put the caret anywhere in a program and the page shows what the checker
has there:

- **Expected**: what the position has to produce.
- **Scope**: every entry in scope, with its type and what it is known
  to equal.
- **Refutations**: at a `match`, the value constructors that are ruled
  out, each with a step-by-step derivation of why.
- **Termination**: the parameters a recursive call has to decrease.

Clicking a term shows its canonical form and the rewrites that lead to
it. The language is deliberately explicit, so that what the checker
does can be followed by hand.

## The language

Pledge is restricted so that it stays small enough to learn whole.
Types never contain function calls, functions are not first class, and
recursion is checked by structural decrease on parameters marked
`subterm`. Proofs are ordinary values: a program states a `goal`,
proves it with `qed`, and the page reports whether the goal is proved.
`sorry` stands in for a missing proof, and the checker tracks what
relies on one.

- [DESIGN.md](DESIGN.md) is the specification.
- [SOUNDNESS.md](SOUNDNESS.md) argues that no program can prove
  `False`. The argument is written out, not machine-checked.

Pledge is loosely based on
[Sleight](https://github.com/emmarion/sleight), a larger language, and
shares none of its code.

## Examples

Longer programs in [examples/](examples/), each checked under phase 2
(which adds erasure), with a goal the checker reports as proved without
`sorry`. The playground's Example menu opens any of them. The
summaries below are a Claude session's reading of what each goal
states.

- [binary.pledge](examples/binary.pledge): binary naturals related to
  unary `Nat`, with addition and multiplication shown to agree with
  their unary counterparts.
- [compiler.pledge](examples/compiler.pledge): a compiler from
  expressions of literals and addition to a stack machine, with
  evidence that running the compiled code pushes the expression's value.
- [prime.pledge](examples/prime.pledge): a definition of primality,
  checked by a proof that a prime's only factorizations involve one,
  and a decision procedure on binary numbers that builds the list of
  primes up to the square root, proved to list exactly the primes; it
  reports a factor of a composite, and `comptime` uses it to prove
  4999 prime.
- [sort.pledge](examples/sort.pledge): insertion sort returning
  evidence that its result is sorted and a permutation of its input.
- [tree23.pledge](examples/tree23.pledge): 2-3 trees whose height is
  in their type, so that, as we understand it, they stay balanced by
  construction; key order is not proved.
- [typesafety.pledge](examples/typesafety.pledge): type safety
  (progress and preservation) of the typed arithmetic language of
  Pierce's *Types and Programming Languages*, chapter 8, as we
  understand that language.

In each, the evidence is erased, so what runs is meant to be only the
computation itself.

## Status

Pledge is a prototype for teaching, not a language for writing
software: it has no strings, no numbers beyond the ones you define, and
no input or output. The language design is the repository owner's. The
implementation, the tutorial and SOUNDNESS.md were written by Claude
sessions and may contain mistakes; where they disagree with DESIGN.md,
DESIGN.md is right. [ASSUMPTIONS.md](ASSUMPTIONS.md) lists the choices
the implementation makes where DESIGN.md is silent.

## Running it locally

The implementation is TypeScript, with no runtime dependencies; its
development dependencies are the compiler, Node's type declarations and
Vite, which builds the site into `dist/`. `./run.sh` pulls, builds, serves
on port 8765 (or the port given as its argument) and, on a Mac, opens
the page. By hand:

```sh
npm install
npm run build
npm run serve      # then open http://localhost:8000/
npm test
```

[INTERNALS.md](INTERNALS.md) describes how the code is laid out. A push
to `main` type-checks, runs the tests and deploys `dist/` to GitHub Pages.

## Citing and license

[CITATION.cff](CITATION.cff) has the citation; the code is at
https://doi.org/10.5281/zenodo.24092650. Apache-2.0, see
[LICENSE](LICENSE) and [NOTICE](NOTICE).
