# Internals

How the implementation is laid out. DESIGN.md is the specification;
this file is a Claude session's description of the code, and where the
two disagree, DESIGN.md is right and the code is wrong. Section numbers
(§) are DESIGN.md's.

## Modules

- `src/syntax.ts`: the abstract syntax (§19 and §16's additions). Every
  node carries a `Span` of offsets into the source string. `Id.name` is `null` for `_`.
  `Term.args` is `null` for a bare name. `Binder.mult` and the other
  `mult` fields are `null` when no multiplicity is written. `let x = e;`
  is parsed as a tuple `let` with one binder (§8).
- `src/lexer.ts`, `src/parser.ts`: source text to `Program`. The lexer
  takes the phase, since `erased` and `many` are keywords only from
  phase 2 (§18). `parse` returns the items before the first syntax
  error together with that error.
- `src/api.ts`: the contract between the checker and the interface
  (§12, §13). `Diagnostic.message` is a thunk (CLAUDE.md rule 17), and
  so is the `derivation` an error from a refuted value constructor
  carries. `Rendered` is display text whose names and anonymous-entry
  markers are linked to entries. `CheckResult.infoAt` answers §13's
  panels for a caret position, `nameAt` says what the name at a
  position refers to, and `explainAt` and `evalAt` serve the Term panel
  and the interactive mode.
- `src/terms.ts`: skeleton terms (entries, bound variables of a
  telescope, applications), the persistent scope of entries, their
  types and `is` rules, canonicalization, identity, the strict-subterm
  relation (§9) and shortest rewrite sequences (§13).
- `src/telescope.ts`: opening telescopes, forcing with refutation
  derivations (§7), the unifier that solves `_` arguments (§16) by
  giving rules only to their own entries, and the comparison of a
  function's telescopes with a function goal's (§12).
- `src/render.ts`: display of terms, entries and telescopes as
  `Rendered`.
- `src/position.ts`: line and column of an offset, and the text an
  offset falls in among several joined by newlines.
- `src/context.ts`: shared checker state, the first-error exception,
  the snapshots behind §13, the record of what each name occurrence
  refers to, and the spans of erased code the editor sets in italics.
- `src/expr.ts`: expressions, statements, telescopes, what a position
  is given (§8), `match` and pattern `let` (§10), the §9 marks,
  per-result taint and erasure (§12, §16), `_` arguments, and the tree
  the interpreter evaluates (§14).
- `src/check.ts`: the top level of the checker: `data` groups, function
  groups with the taint fixed point (§12), top-level statements,
  evaluation of each statement as it is checked (§11), `goal` and
  `qed`.
- `src/goal.ts`: what a `qed` is given, and `qed f;` against a function
  goal (§12).
- `src/eval.ts`: the tree-walking interpreter (§11, §14).
- `src/info.ts`: `infoAt`, `nameAt`, `explainAt`, `evalAt`, and what
  the Scope panel lists.
- `src/examples.ts`: the `Nat`, `Vec` and `vhead` sources shared by the
  tutorial and the tests, the front page's starting program, and the
  titles its Example menu gives the programs in `examples/`, each taken
  from the first line of the program's header comment.
- `src/ui/`: the page (§13) and the tutorial page (§12). `main.ts`
  bundles every `examples/*.pledge` into the page with Vite's
  `import.meta.glob`.
- `src/ui/worker.ts`, `src/ui/remote.ts`: the pages check in Web
  Workers, so that a long check does not block the page. A worker runs
  `check` once, replies with the result's plain fields and the kind of
  each name occurrence, keeps the `CheckResult`, and then answers
  `infoAt`, `nameAt`, `explainAt` and `evalAt` by message. Every thunk
  in a reply (message texts, derivations) is forced when the reply is
  sent and arrives as a thunk again. Each check gets a new worker: an
  edit terminates a check that is still running, and the worker of the
  last finished check goes on answering until the next one finishes.
- `src/ui/editor.ts`: the editor. It repaints by line, and keeps the
  elements of the lines that did not change.
- `src/tutorial/`: the tutorial as data. `pages.ts` has the `Page` type
  and assembles the sections; `start.ts`, `dependent.ts`,
  `recursion.ts`, `evidence.ts`, `relation.ts`, `arithmetic.ts`,
  `limits.ts`, `erasure.ts` and `appendix.ts` hold one section each, in
  that order; `programs.ts` holds the program snippets that sections
  share; `glossary.ts` holds the glossary.
- `src/ui/links.ts`: the links that citations of DESIGN.md get, and the
  rendering of prose and messages (code between backticks, citations as links).
- `examples/`: longer Pledge programs, checked by the tests under
  phase 2 and offered by the front page's Example menu.
- `tests/`: Pledge programs the tests check (`.pledge`); `helpers.ts`
  and `tutorial.ts`, which the test files share; and `Beyond.agda`,
  the Agda file the tutorial's page "What Pledge leaves out" quotes.

## The Lean implementation

`lean/` holds a second implementation of the checker and evaluator, in
Lean 4, and Lean-checked soundness theorems about it for phase 1
programs without `sorry`; `lean/README.md` describes its layout, what
is proved and how it differs from the code above. It shares no code
with `src/`. `lean/tests/` compares its verdicts with those of
`src/check.ts` on a corpus of programs that `lean/tests/gen-corpus.mjs`
collects from the test suite, `tests/*.pledge` and the tutorial.
