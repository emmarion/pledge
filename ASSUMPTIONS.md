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
2. **Build.** Vite builds the pages in `web/` into `dist/`, which is
   not committed; `tsc` only type-checks. Tests are `node --test` over
   `src/**/*.test.ts`, run on the TypeScript directly by Node's type
   stripping, with imports written with the `.ts` extension. Since type
   stripping checks no types, `npm run typecheck` checks the tests too,
   under `tsconfig.test.json`.
   The GitHub Actions workflow in `.github/` type-checks, tests, builds
   and deploys `dist/` to GitHub Pages.
3. **Positions** in the interface (§13) are offsets into the source
   as a JavaScript string, which for ASCII source are also byte
   offsets; the editor is a plain `textarea`, and the selected position
   is the caret. No editor library is used.
4. **Dependencies.** The only dependencies are TypeScript itself,
   Node's type declarations, which the tests are type-checked against,
   and Vite, all development dependencies.
14. **`tests/design_reflection.pledge`** supplies a `decideEven`
    whose header is §11's, delegating to a recursive helper, since
    DESIGN.md gives only the signature.

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
7. **Evaluation is a loop over an explicit stack**, so JavaScript's
   stack does not bound a run's depth, and a call in tail position, the
   final expression of a body, block or branch, runs in constant space.
   Non-tail depth is bounded by the heap. DESIGN.md sets no depth and
   says nothing about tail calls.
8. **Values are shown** as `C(a1, a2)`, with `, ` between arguments;
   §12 does not fix the spacing.

## Syntax

9. **Extra `;`** (§1) is read as allowed after the `}` that closes a
   `data`, `fn` or `mutual` declaration and after a block's final
   expression when that expression ends in `}`; any `;` can be
   followed by more. A `;` with nothing before it, at the start of
   the program or of a block, is rejected. This may be stricter or
   looser than intended.
11. **`_` as an erased argument** (§16) is accepted only as a whole
    argument of a call or application in an expression, in phase 2;
    not inside a skeleton term such as `Vec(_, n)`, and not as a tuple
    element. Under phase 1, a `_` argument, and a syntax error on the
    token after a name spelled `erased` or `many`, are reported as
    phase 2 syntax; the second can mislead where the name is an
    ordinary one.
12. **Lexing.** A maximal run of letters, digits and `_` is one token;
    one not starting with a letter, other than `_` alone, is an error
    rather than being split. Any non-ASCII character is an error, in a
    comment too. A lexical error is reported only when the parser
    reaches it, so an earlier syntax error wins (§13's first error).
    `Type` is lexed as a name, not a keyword (§18).
13. **Spans.** A statement, value-constructor declaration or branch
    spans through its own `;` but not extra ones; a binder's span
    includes its `subterm` mark and multiplicity.

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
19. **Refutation derivations** (§13). Forcing processes its equations
    first in, first out, the scrutinee's before the type's, and a
    derivation numbers its lines in that order. That a derivation has
    the fewest steps is presumed, not proved. A line does not list a
    rewrite by the anonymous entry of an application written in place,
    or of a `_` already solved.
20. **Anonymous entries** render as `?kind@line:col`, with the kind the
    checker gives the entry's origin, and as `?kind@boxN:line:col` on a
    tutorial page, where the interface supplies the position format;
    two anonymous entries of the same kind at the same position are not
    told apart, so the checker chooses distinct kinds.
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
24. **The term at the caret** (§13) is explained in a panel of its
    own, Term, which follows the caret as the other panels do; clicking
    a term is one way of putting the caret on it. A name in a panel
    moves the caret to the entry's origin, since a panel has no source
    offset. The interactive mode's field is a panel too, At the caret;
    its answer is recomputed when the caret moves, when the program is
    rechecked and as the learner types in the field.
25. **The learner's text** and the chosen phase are kept in
    `localStorage`, with a button to restore the starting text, which
    asks before it replaces text that was changed; checking runs
    shortly after the last edit, and the panels follow the caret
    without rechecking.
43. **Syntax highlighting** lexes each box under the page's phase, so
    `erased` is coloured as a name in phase 1 and a keyword in phase 2.
    A name is coloured by what the checker says that occurrence refers
    to (type constructor, value constructor, function); locals and
    top-level bindings keep the text colour. Where the checker gives no
    answer, in text after the first error or while an edit awaits its
    check, a name keeps the colour it last resolved to rather than
    flickering off; printed values are coloured from the same memory.
44. **Beside the editor**, an output wraps onto free lines below its
    own and otherwise ends in an ellipsis, opening in full on hover or
    focus. In a window narrower than 1200 pixels the outputs are listed
    below the box instead, each with its line number. Hovering a name
    shows what the checker says that occurrence refers to: an entry's
    type and `is` rule, where the name is used and where it is bound,
    or the signature of a function, type constructor or value
    constructor. A binding occurrence is described in the scope after
    its whole `let`, pattern or telescope binder.
62. **An error from a refuted value constructor** carries the
    derivation of the refutation (§13) apart from its message; the
    status line lists it under the message, and beside the statement
    only the message is shown. In a message, as in the tutorial's
    prose, text between backticks is shown as code and a citation is a
    link (item 61); a message writes every name and term of the program
    that way. A message about a result that does not fit what its
    position is given names the binder with its role and owner, as in
    "parameter `v` of `vhead`", and so does a message about an erased
    value where none is allowed; a `qed`'s position is called "the
    goal's proof".
63. **A tainted scope** is reported in the Scope panel by one line
    above the entries, linking to the scrutinee whose taint reached
    the position first, the outermost when several did. A tainted name
    carries a `tainted` tag after it, in the panel and in the hover
    tip.
65. **Layout.** The widths at which the layout changes are chosen so
    that no box cuts a line of the tutorial's 72 columns. From 1440
    pixels the list of pages is a column of its own, and below that a
    closed disclosure above the page. Below 1200 the outputs go under
    their box and the panels' column narrows, and it narrows again
    below 1010. Below 955 the panels go under the boxes. On a page
    with several boxes each box shows its number, since positions cite
    boxes by number.
68. **Without JavaScript**, each page shows a description of itself and
    links, from a `<noscript>` block, and carries a description for
    link previews. The front page's block repeats the starting example,
    which a test compares with the example the page loads; with
    JavaScript the front page opens with a sentence saying what it is
    and pointing to the tutorial.

## Tutorial

26. **Solutions.** Each tutorial page carries a solution, shown in a
    closed "Show a solution" disclosure below the learner's box as a
    read-only box of its own; §12 says nothing about solutions. The
    caret in it makes the panels and the status describe a second
    program, the fixed boxes followed by the solution, checked under
    the page's phase and ignoring the learner's box; the status says
    which program it describes. The fixed boxes' outputs come from the
    learner's program.
27. **Starting texts** of several pages do not check (a missing branch,
    a wrong `is`, unmarked recursion), so the learner first sees the
    checker's error; §12 does not say whether a page's starting text
    should check.
28. **Stating `plus(n, Zero())` equals `n`.** Since a type contains no
    call (§3), the tutorial states it through a data type constructor
    `Plus(m, n, r)`, with `plus` returning its result together with a
    `Plus` value, and proves `Eq(Nat(), r, n)` from `Plus(n, Zero(), r)`.
    This is a session's reading of how such a fact is meant to be
    expressed; the owner may intend another idiom. The page "Appending
    vectors" follows it where a type would need a call: `vappend`
    returns the result's length and a `Plus` value with the vector.
29. **Names.** `Bool`'s value constructors are `True` and `False`, and
    the empty type on a later page is also `False`; they never share a
    program. The solution of the page "Why Pledge appears sound" uses
    `sorry` deliberately, so its goal stays unproved.
59. **The arithmetic pages** state everything relationally: `Plus(m,
    n, r)` as on the proof-by-recursion page, and `Times(m, n, r)`
    with recursion on the first argument, `TimesSucc` needing
    `Times(m, n, r)` and `Plus(r, n, s)` for `Times(Succ(m), n, s)`.
    Existential witnesses are extra returns. Distributivity is proved
    through an `exchange` lemma, (w + y) + (x + z) = (w + x) + (y + z),
    whose `let`s give each proof's type, mentioning the witnesses bound
    before it in the same `let`. The shown proofs sit in the learner's box,
    with `sorry(_)` in the branches the learner is to write, since a
    function cannot be split between a read-only box and the learner's
    box.
60. **The phase 2 pages** erase, in the example types, `VNil`'s and
    `VCons`'s `A`, `VCons`'s `n` and both fields of `Refl`, as the
    phase 2 example programs under `tests/` do; §16 does not say which
    fields should be erased. Where their prose describes behaviour
    DESIGN.md is silent on, it says "in this implementation".
64. **Sections.** The tutorial's pages are grouped under headings in
    the list of pages, each page shows its section above its title, a
    page checked under a later phase carries a tag saying so in the
    list, and the appendix's heading is marked optional; §12 says
    nothing about how pages are arranged.
66. **A page's task and the glossary.** A tutorial page shows its task
    in a block of its own, and offers a glossary of the terms the
    tutorial defines, each with the page that defines it. The
    glossary's definitions are a session's paraphrases of DESIGN.md.
67. **The closing page**, "What Pledge leaves out", compares Pledge
    with Agda. Its Agda code is an abridgement of `tests/Beyond.agda`,
    which a session compiled with Agda 2.6.3; the tests check that the
    page's lines occur in that file, not that the file compiles. What
    the page says of Lean and Idris is a session's understanding.
61. **Citations in the tutorial's prose**, of a section (§) or of
    DESIGN.md or SOUNDNESS.md, link to the file on the `main` branch
    of the repository on GitHub, a section by its heading's anchor.
    Each page lists the sections its claims rest on in a line under its
    task; the main path's prose cites none inline, and the appendix's
    does.

## Checking

31. **Inside one body**, after a pattern `let` whose scrutinee is
    tainted, every result produced later in checking order is tainted,
    later parts of the same statement included; results produced
    earlier in that statement are not, though the statement is never
    evaluated. §12 speaks of the body's results and does not mention
    the statement holding the pattern `let`.
32. **A later error** anywhere in the program leaves the goal unproved,
    even when the `qed` checked before it; §12 does not say.
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
39. **What the status reads off the text.** Whether the program
    contains `sorry`, `qed` or `goal` is read off the tokens, so it
    stands when the program does not parse; a keyword after a lexical
    error is not seen, since the lexer stops there. A `qed`'s
    expression is evaluated as any top-level statement, its value
    discarded; `qed sorry(_);` is allowed (§14).
40. **An exception from the evaluator**, such as running out of
    memory on a deep recursion, is reported as the program's error at
    the statement being evaluated.
41. **§13 snapshots.** Information is recorded at every expression,
    statement, binder and declaration, and `infoAt` answers from the
    smallest recorded span containing the position. Refutations are
    shown at the `match` or pattern `let` itself. For what Scope lists,
    a `mutual` block is one declaration and so is a function goal, and
    a position in the text after a syntax error has the top-level
    scope that follows the last item checked. Anonymous entries are
    labelled by origin: `app`, `param`, `binder`, `f.r` for return `r`
    of a call to `f`, `match.r`, `sorry.r` and `C.f` for a forced
    field.
42. **Within a group**, bodies are re-checked until no further function
    becomes tainted, and the §13 information is kept from the final
    pass only.

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
    A block's final expression takes part in solving a `_` of the
    application the block is an argument of, as a direct argument
    does; the block's statements and a match branch's body do not.
53. **Scope and Expected panels** mark an entry erased when it was
    opened erased or every one of its names was bound erased.
    Interactive mode checks typed text as in an erased position, since
    it never evaluates.

## Function goals (§12)

55. **What `qed f;` is.** Against a function goal, the `qed`'s
    expression must be the bare name of a function declared before it;
    any other expression, `qed sorry(_);` included, is an error, so a
    learner who wants to give up writes a function whose body is
    `sorry(_)`. `qed f;` against a type goal is an error. Nothing is
    evaluated at such a `qed`.
56. **Comparing telescopes at `qed f;`** (§12) happens in
    the scope at the `qed`, so facts in force there count. A mismatch is
    an error at the name, so the `qed` does not check, and the message
    names the first position that differs.
57. **Taint.** The goal is tainted as a telescope is; the function's
    taint is its body's (§12), so a function whose own telescopes
    mention a tainted binding is not tainted by that. The alternative,
    also requiring the function's telescopes to be untainted, is open.
58. **Panels.** At the `qed`'s name, Expected shows the goal's
    parameters, then its returns; inside the goal's telescopes the
    panels work as inside a function's, with no enclosing function.
