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

## Syntax

9. **Extra `;`** (§1) is read as allowed after the `}` that closes a
   `data`, `fn` or `mutual` declaration and after a block's final
   expression when that expression ends in `}`; any `;` can be
   followed by more. A `;` with nothing before it, at the start of
   the program or of a block, is rejected. This may be stricter or
   looser than intended.
10. **Where a multiplicity goes** (§16, phase 2): immediately before
    the binder's name, after `subterm`, as `[subterm] [erased|many]
    name`, for parameters, returns, value-constructor fields, match
    annotation entries and each tuple-`let` binder (`let (erased a,
    b) = e;`). `let erased C(...) = e;` and `comptime let erased
    C(...) = e;` give a pattern `let` a multiplicity, by analogy with
    `match erased e`. An explicit `many` is accepted wherever `erased`
    is. No multiplicity is accepted on type-constructor parameters,
    on `sorry`'s telescope, on a pattern's fields, or before a whole
    tuple `let`.
11. **`_` as an erased argument** (§16) is accepted only as a whole
    argument of a call or application in an expression, in phase 2;
    not inside a skeleton term such as `Vec(_, n)`, and not as a tuple
    element.
12. **Lexing.** A maximal run of letters, digits and `_` is one token;
    one not starting with a letter, other than `_` alone, is an error
    rather than being split. Any non-ASCII byte is an error, in a
    comment too. A lexical error is reported only when the parser
    reaches it, so an earlier syntax error wins (§13's first error).
    `Type` is lexed as a name, not a keyword (§18).
13. **Spans.** A statement, value-constructor declaration or branch
    spans through its own `;` but not extra ones; a binder's span
    includes its `subterm` mark and multiplicity. A `_` standing for a
    whole telescope has no span of its own, so an error about it
    points at the enclosing `match` or `sorry`.
14. **`tests/design_reflection.pledge`** supplies a `decideEven`
    whose header is §11's, delegating to a recursive helper, since
    DESIGN.md gives only the signature.

## Terms, scope and forcing

15. **Bound variables** in a telescope are indexed by position in the
    whole environment the telescope is opened or instantiated under
    (an outer prefix such as the parameters, then its own binders), so
    a return telescope continues the parameters' numbering.
16. **Entries and applications.** Types, rules and canonical forms are
    trees of applications with entries at the leaves; §7's "every
    application is an entry" holds for applications written as
    expressions, each of which gets an entry whose rule is the
    application, and canonicalization unfolds such entries, so the two
    forms compare equal.
17. **Where a fact was created** (§13): an `is` rule from opening a
    binder is attributed to the place the binder is opened, such as
    the call, not to where it is written; a forcing rule to the
    pattern.
18. **A rewrite step** (§13) rewrites every occurrence of one entry by
    its rule at once, so the shortest sequence rewrites each entry the
    term reaches once, outer entries first. If a step is meant to
    rewrite one occurrence, the count would differ.
19. **Refutation derivations** (§13) are the chain of equations from
    an initial equation of forcing to the first failing one, equations
    being processed first in, first out, the scrutinee's before the
    type's. That this has the fewest steps is presumed, not proved.
20. **Anonymous entries** render as `?kind@line:col`, with the kind the
    checker gives the entry's origin; two anonymous entries of the same
    kind at the same position are not told apart, so the checker
    chooses distinct kinds.
21. **Forcing two applications with the same head but different
    argument counts**, impossible for well-formed terms, is treated as
    a refutation by different heads rather than an internal error.
