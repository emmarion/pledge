# Implementation assumptions log

A running log of the choices the implementation (`src/`, `web/`) makes
where DESIGN.md is silent or ambiguous, or where it takes a shortcut.
Written by Claude sessions working autonomously at the owner's request;
nothing here is a design decision (CLAUDE.md rules 11 and 14). Every
item is a candidate question for the owner, and the owner's answer may
well be different from what the code does. Items are cited by number
and never renumbered (rule 15); a removed item leaves a gap.

## Project shape

1. **Source files** of Pledge programs use the extension `.pledge`.
   DESIGN.md names no extension; `.pl` would collide with Perl and
   Prolog.
2. **Build.** The TypeScript is compiled by `tsc` alone, to native ES
   modules that the page loads without a bundler; the compiled
   `web/js/` is not committed. Tests are `node --test` over
   `src/**/*.test.ts`, run on the TypeScript directly by Node's type
   stripping, with imports written with the `.ts` extension and
   rewritten by `tsc` on output. The GitHub Actions workflow in
   `.github/` builds and deploys `web/` to GitHub Pages; the owner has
   to enable Pages for the repository.
3. **Positions** in the interface (§13) are byte offsets into the
   source; the editor is a plain `textarea`, and the selected position
   is the caret. No editor library is used.
4. **Dependencies.** The only dependency is TypeScript itself, as a
   development dependency.

## Evaluation

5. **A function body sees the top-level bindings** written before the
   function, as well as its parameters: §1 lets a binder refer to any
   entry in scope, a top-level one included, and "no closures" (§8) is
   read as being about local bindings. Each function is evaluated in
   the top-level value environment in force where it was declared.
6. **Removed expressions** (§12, §14) evaluate to one sentinel value,
   expanded to as many as the position needs where that number is
   known. The sentinel is allowed as an argument, in a field and in a
   binding, and `showValue` shows it as `_` (§16's erased fields);
   reading its tag, at a match or a pattern `let`, is an internal
   error, on the reading that taint and erasure guarantee it never
   happens.
7. **Evaluation recurses on the JS stack.** `ack(3, 6)` evaluates,
   `ack(3, 7)` overflows Node's default stack. DESIGN.md sets no depth,
   and the prototype does not try to (rule 6).
8. **Values are shown** as `C(a1, a2)`, with `, ` between arguments;
   §12 does not fix the spacing.
