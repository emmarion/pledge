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

## Interface

22. **A tutorial page** (§12) joins its read-only boxes and the
    learner's box with one newline between them into one program,
    and maps each span back to the box containing its start. A page
    that requires the `qed` in the learner's box lexes that box for
    the keyword; when it is missing, the status reports no `qed` in
    the box and the goal as not proved, whatever the checker says of
    the whole program.
23. **Output beside a statement** (§12, §13) is a column to the right
    of the editor aligned with the line where the statement starts; an
    `inspect;` there is a closed disclosure that opens the §13 panels,
    a liberal reading of "as text".
24. **Clicking a term** in the source explains the term at that offset
    (§13); a name in a panel moves the caret to the entry's origin and
    explains the term there, since a panel has no source offset.
25. **The learner's text** and the chosen phase are kept in
    `localStorage`, with a button to restore the starting text;
    checking runs shortly after the last edit, and the panels follow
    the caret without rechecking.

## Tutorial

26. **Solutions.** Each tutorial page carries a solution, shown in a
    closed "Show a solution" disclosure below the learner's box; §12
    says nothing about solutions.
27. **Starting texts** of several pages do not check (a missing branch,
    a wrong `is`, unmarked recursion), so the learner first sees the
    checker's error; §12 does not say whether a page's starting text
    should check.
28. **Stating `plus(n, Zero())` equals `n`.** Since a type contains no
    call (§3), the tutorial states it through a data type constructor
    `Plus(m, n, r)`, with `plus` returning its result together with a
    `Plus` value, and proves `Eq(Nat(), r, n)` from `Plus(n, Zero(), r)`.
    This is a session's reading of how such a fact is meant to be
    expressed; the owner may intend another idiom.
29. **Names.** `Bool`'s value constructors are `True` and `False`, and
    the empty type on a later page is also `False`; they never share a
    program. The closing page's solution uses `sorry` deliberately, so
    its goal stays unproved.

## Checking

30. **Tuple `let` binders** are not a telescope: each binder's type or
    `is` clause is checked in the scope before the `let`, since §8
    puts the binders in scope only after it, so
    `let (a : Nat(), b is Succ(a)) = e;` is rejected.
31. **What survives a block.** §7 and §8 seem not to say what happens
    to the entries a block creates, though its results can be such
    entries. The checker keeps every entry created in the block, with
    the rules it has at the block's end, and drops the rules the block
    added to older entries (related to DECISIONS.md O5). In a block
    whose results are tainted by a pattern `let` inside it, a kept
    entry's rules can be inconsistent with the facts outside; a review
    found no way to reach such an entry from an untainted value, but
    this is an open question rather than a proof.
32. **A later error** anywhere in the program leaves the goal unproved,
    even when the `qed` checked before it; §12 does not say.
33. **Functions declared after a tainted top-level pattern `let`** are
    not tainted by it, §12's rule speaking of top-level statements;
    this seems harmless since nothing evaluates after that `let`.
34. **Every top-level `let` is evaluated** as DESIGN.md §11 says;
    SOUNDNESS.md part 8 says ordinary top-level `let`s are never
    evaluated, which the two files should settle between them.
35. **Taint of `goal`'s type**, a skeleton term, is computed as for an
    expression: a variable is tainted when it names a tainted binder,
    an application when an argument is.
36. **Order of declarations.** A type constructor's own name is not in
    scope in its parameter telescope, nor a value constructor's in its
    fields; a group's functions are all registered, then all their
    telescopes checked in written order, then their bodies.
37. **Positions given nothing** (a scrutinee, a pattern `let`'s
    right-hand side, `print`'s expression) must produce exactly one
    value, reading §8's "anywhere else".
38. **The first error** is the first the checker meets in its own order,
    not the first in text order: a group's telescopes before its
    bodies, and a match's patterns before its branch bodies.
39. **`qedChecks`** is false, not null, when checking stops before the
    `qed`. **`containsSorry`** is read off the tokens, even when the
    program does not parse. A `qed`'s expression is evaluated as any
    top-level statement, its value discarded; `qed sorry(_);` is
    allowed (§14).
40. **An exception from the evaluator**, such as a JavaScript stack
    overflow on a deep recursion, is reported as the program's error at
    the statement being evaluated.
41. **§13 snapshots.** Information is recorded at every expression,
    statement, binder and declaration, and `infoAt` answers from the
    smallest recorded span containing the position. The Scope panel
    lists every entry in scope, top-level ones included, but not
    anonymous application entries; refutations are shown at the
    `match` or pattern `let` itself. Anonymous entries are labelled by
    origin: `app`, `param`, `binder`, `f.r` for return `r` of a call to
    `f`, `match.r`, `sorry.r` and `C.f` for a forced field.
42. **Within a group**, bodies are re-checked until no further function
    becomes tainted, and the §13 information is kept from the final
    pass only.
43. **Syntax highlighting** lexes each box under the page's phase, so
    `erased` is coloured as a name in phase 1 and a keyword in phase 2.
    Names are coloured by what the last check's Globals say they are
    (type constructor, value constructor, function); locals and
    top-level bindings keep the text colour. When a program does not
    parse, the previous colouring is kept rather than flickering off.
44. **Beside the editor**, an output wraps onto free lines below its
    own and otherwise ends in an ellipsis, opening in full on hover or
    focus. Hovering a name shows its entry's type and `is` rule, or a
    global's signature.

## Erasure (phase 2)

45. **Erased results, not only names.** §16's "erased name" is read as
    any erased result: a name bound erased, a call's result for an
    erased return, a match's result for an erased annotation entry,
    and a `_`. Each is allowed only where its position is erased.
46. **Erasure flows down per result.** A position's result is erased
    when what the position is given has an erased entry there, and
    for every argument of a type constructor. A tuple passes it to
    its elements, a block to its final expression, a match to the
    matching result of every branch body; a call's arguments take
    their parameters' multiplicities, never the call's position. An
    expression whose results are all in erased positions is wholly
    erased, everything inside it included; §16's "a call whose results
    are all erased takes any arguments" follows from this.
47. **Positions given nothing are `many`**: a `many` match's scrutinee,
    a `many` pattern `let`'s right-hand side, `print`'s and `qed`'s
    expressions. So `print x;` and `qed x;` with `x` erased are errors.
48. **The one-branch rule** applies to every `match erased` with a
    `many` annotation entry, even when the whole match is in an erased
    position and never runs. `comptime let erased C(...) = e;` is
    rejected, since the run needs the value.
49. **Type-constructor arguments** are removed before evaluation like
    any erased position, so `print Vec(Nat(), Zero());` shows
    `Vec(_, _)` in phase 2.
50. **`sorry`'s telescope** takes no multiplicities; `sorry(_)` takes
    those of the telescope it stands for.
51. **`_`** is allowed only for an argument whose parameter or field is
    erased, or a type constructor's argument. It gets a fresh erased
    entry typed by its parameter. Wherever a result is checked against
    what its position is given, the two sides are first unified by
    forcing's equation engine, which here gives a rule only to the
    entry of a `_` still being solved. When the application ends,
    every `_` created for it must be solved, unless what the position
    is given mentions a `_` of an enclosing application, which then
    solves it; a solution must have the parameter's type and satisfy
    its `is` clause, as a written argument would, and must mention
    only entries created before the `_`. This last rule is what keeps
    a `_` from being solved to a result of the very call it is an
    argument of; it also rejects a `_` determined only by a later
    argument's call result, and it still accepts a solution naming an
    earlier argument's call result, which no written argument could.
    A block used as an argument never helps solve a `_` of the
    enclosing application, even when the block contains no `_`, so
    `g(_, { v }, Zero())` is rejected where `g(_, v, Zero())` is
    accepted; a match or a tuple there is fine. Whether a block should
    take part is an open question for the owner: it would mean
    unifying the block's results with what it is given in the outer
    scope, after the block's facts end.
52. **Taint through `_`.** A `_` whose canonical solution mentions an
    entry that is tainted, or that has a tainted name, taints the
    application. This is stricter than §12's rule for a written
    argument: when an entry has both a clean name `n` and a tainted
    one, `k(n, _)` is tainted where `k(n, n)` is not. It is also looser
    in one direction: with `x` from `sorry(x is Zero())`, `k(Zero(), _)`
    is untainted though `k(Zero(), x)` is tainted, since the solution
    is the ground term `Zero()`. Both only matter in programs that
    contain `sorry`.
53. **Scope and Expected panels** mark an entry erased when it was
    opened erased or every one of its names was bound erased; `_`
    entries are hidden like anonymous application entries. Interactive
    mode checks typed text as in an erased position, since it never
    evaluates.

## Function goals (DECISIONS.md D43)

54. **Syntax.** `goal fn (params) -> (returns);` is parsed exactly as a
    function's two telescopes, so `subterm` marks, `_` names and, in
    phase 2, multiplicities are accepted; there is no name and no body.
55. **What `qed f;` is.** Against a function goal, the `qed`'s
    expression must be the bare name of a function declared before it;
    any other expression, `qed sorry(_);` included, is an error, so a
    learner who wants to give up writes a function whose body is
    `sorry(_)`. `qed f;` against a type goal is an error. Nothing is
    evaluated at such a `qed`.
56. **Identity of telescopes.** The goal's parameters and returns are
    opened as one telescope in the scope at the `qed`, its `is` clauses
    as rules, and the function's binders are compared position by
    position, canonically, with `is` clauses both absent or both
    present and identical, and multiplicities equal. So an earlier
    binder's `is` clause counts for later ones, `x : Nat()` differs from
    `x is Zero()`, and facts in force at the `qed`, including those of
    untainted top-level pattern `let`s after the `goal`, count. A
    mismatch is an error at the name, so `qedChecks` stays false, and
    the message names the first position that differs.
57. **Taint.** The goal is tainted as a telescope is; the function's
    taint is its body's (§12), so a function whose own telescopes
    mention a tainted binding is not tainted by that. The alternative,
    also requiring the function's telescopes to be untainted, is open.
58. **Panels.** At the `qed`'s name, Expected shows the goal's
    parameters, then its returns; inside the goal's telescopes the
    panels work as inside a function's, with no enclosing function.
