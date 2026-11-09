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
  phase 2 (§18).
- `src/api.ts`: the contract between the checker and the interface
  (§12, §13). `Diagnostic.message` is a thunk (CLAUDE.md rule 17), and
  so is the `derivation` an error from a refuted value constructor
  carries. `Rendered` is display text whose names and anonymous-entry
  markers are linked to entries. `CheckResult.infoAt` answers §13's
  panels for a caret position; `explainAt` and `evalAt` serve the
  click-to-explain and interactive features.
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
- `src/position.ts`: line and column of an offset.
- `src/context.ts`: shared checker state, the first-error exception and
  the snapshots behind §13.
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
- `src/info.ts`: `infoAt`, `explainAt`, `evalAt`.
- `src/examples.ts`: the `Nat`, `Vec` and `vhead` sources shared by the
  page's starting program, the tutorial and the tests.
- `src/ui/`: the page (§13) and the tutorial page (§12).
- `src/tutorial/pages.ts`: the tutorial's pages as data.
- `src/ui/links.ts`: the links that citations of DESIGN.md get, and the
  rendering of prose and messages (code between backticks, citations as links).
- `tests/`: Pledge programs the tests check (`.pledge`), and
  `helpers.ts`, which the test files share.
