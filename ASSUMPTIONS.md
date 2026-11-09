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
