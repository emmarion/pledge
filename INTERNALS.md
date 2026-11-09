# Internals

How the implementation is laid out. DESIGN.md is the specification;
this file is a Claude session's description of the code, and where the
two disagree, DESIGN.md is right and the code is wrong. Section numbers
(§) are DESIGN.md's.

## Modules

- `src/syntax.ts`: the abstract syntax (§19 and §16's additions). Every
  node carries a `Span` of byte offsets. `Id.name` is `null` for `_`.
  `Term.args` is `null` for a bare name. `Binder.mult` and the other
  `mult` fields are `null` when no multiplicity is written. `let x = e;`
  is parsed as a tuple `let` with one binder (§8).
- `src/lexer.ts`, `src/parser.ts`: source text to `Program`. The lexer
  takes the phase, since `erased` and `many` are keywords only from
  phase 2 (§18).
- `src/api.ts`: the contract between the checker and the interface
  (§12, §13). `Diagnostic.message` is a thunk (CLAUDE.md rule 17).
  `Rendered` is display text whose names and anonymous-entry markers
  are linked to entries. `CheckResult.infoAt` answers §13's panels for
  a caret position; `explainAt` and `evalAt` serve the click-to-explain
  and interactive features.
- `src/check.ts` and its helpers: the checker (§3 to §12), which also
  computes taint (§12) and builds the tree the interpreter evaluates
  (§14).
- `src/eval.ts`: the tree-walking interpreter (§11, §14).
- `src/ui/`: the page (§13) and tutorial pages (§12).
- `tests/`: Pledge programs used by the tests, with `.pledge` files.
