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
- `src/terms.ts`: skeleton terms (entries, bound variables of a
  telescope, applications), the persistent scope of entries, their
  types and `is` rules, canonicalization, identity, the strict-subterm
  relation (§9) and shortest rewrite sequences (§13). `src/telescope.ts`:
  opening and instantiating telescopes, applications, and forcing with
  refutation derivations (§7). `src/render.ts`: display of terms,
  entries and signatures as `Rendered`.
- `src/check.ts`: the top level of the checker: `data` groups, function
  groups with the taint fixed point (§12), top-level statements,
  evaluation of each statement as it is checked (§11), `goal` and
  `qed`. `src/expr.ts`: expressions, statements, telescopes, what a
  position is given (§8), `match` and pattern `let` (§10), the §9
  marks, per-result taint, and the tree the interpreter evaluates
  (§14). `src/context.ts`: shared checker state, the first-error
  exception and the snapshots behind §13. `src/info.ts`: `infoAt`,
  `explainAt`, `evalAt`.
- `src/ui/`: the page (§13) and the tutorial page (§12); `src/tutorial/pages.ts`
  holds the tutorial's pages as data.
- `tests/`: Pledge programs used by the tests, with `.pledge` files.
