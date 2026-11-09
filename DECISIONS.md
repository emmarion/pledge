# Decisions not yet in DESIGN.md

A Claude session keeps this file. Its entries are the session's
paraphrases of the owner's decisions in chat. They are not approved
DESIGN.md wording, and are never copied into DESIGN.md as they stand
(CLAUDE.md rule 12). Each decision leaves this file once DESIGN.md
states it. Proposals are recorded with their proposed answers, each
marked as not approved; this file is the one exception to CLAUDE.md
rule 11 (rule 21).

Entries are cited by number. A removed number stays a gap and is never
reused.

## Decided

D10, D11, D13, D22, D24, D26, D27 and D28 stay here although
DESIGN.md covers them, because it states them only as P14 to P16
reword them; each leaves when those proposals are settled.

D10. Taint is decided statically, from the text, without evaluation.
     It comes from what an entry is built from, never from
     canonicalization:
     - every result of `sorry` is tainted;
     - an application, tuple, block or match result is tainted when
       anything it is built from is, a match's scrutinee included;
     - a pattern `let` whose scrutinee is tainted taints every result
       of its block;
     - a function is tainted when a tainted entry reaches any of its
       results in its body (one bit per function);
     - all of a call's results are tainted when the function is tainted
       or any argument is;
     - a tuple `let` binder is tainted when the result it
       binds is tainted;
     - nothing else is tainted; for recursion, everything starts
       untainted, with no special case for `mutual` groups.
D11. A tainted top-level tuple `let` evaluates nothing, and
     its binders are tainted. A tainted `comptime` pattern `let`
     evaluates nothing and skips the check that the result is headed
     by its value constructor; after it, nothing evaluates and no `qed`
     proves the goal.
D13. `goal T;` is checked in the scope where it is written. The goal is
     proved when the `qed` checks, `T` mentions no tainted entry, `e`'s
     result is untainted, and no tainted top-level `comptime` pattern
     `let` comes before the `qed`.
D15. DESIGN.md does not use "expects" or "expected telescope". Where a
     telescope is given is stated by listing the positions.
D16. DESIGN.md never says bare "constructor", and avoids "may" where
     permission and possibility could be confused.
D22. Where a position has no telescope to produce, the Expected panel
     shows an explicit indication that none has been determined there.
D24. A function that only references a taint through a no-op rename is
     untainted, and anyone can call it without taint. The program is
     still reported as containing `sorry` (D8).
D26. Tainted code is stripped before evaluation. The owner's example:
     an unread `let` whose right-hand side is a match on a `sorry`
     scrutinee.
D27. After a top-level pattern `let`, plain or `comptime`, whose
     scrutinee is tainted, nothing evaluates, every `print` shows
     `sorry`, and no `qed` proves the goal, though checking goes on: it
     acts on the rest of the program as D10's pattern-`let` rule acts
     on the rest of a block.
     This extends D11 and D13 to the plain pattern `let`.
D28. How stripping (D26) works: before anything is evaluated, every
     tainted entry is removed together with the computation that would
     produce it, so evaluation never reaches a `sorry`.
D35. For D16's "may": DESIGN.md says "is allowed to" for permission and
     "can" for possibility, as in "no program can prove `False`",
     applied to each section as the section-by-section pass reaches it.

## Approved rules awaiting wording

None at present.

## Proposals, not approved

DESIGN.md applies every proposal below except P3.

P3. The Scope panel shows whether each entry is tainted.
P10. §14 says erased positions exist from phase 2 on.
P11. The positions where a whole telescope is given, so where `_` is
     allowed under D41: a function body (the returns), a branch body
     (the annotation), a block's final expression at one of these
     positions, the right-hand side of a tuple `let` whose binders all
     carry a type or an `is` clause (those binders), and, as an
     implementation choice (D42), a `qed`'s expression (the goal).
P12. What taint removes is left out of the tree the interpreter
     evaluates, as erased positions are from phase 2 on (§14).
P13. Answering O2: the Globals do not mark a top-level binding
     `comptime` or not. Every top-level `let` is evaluated (D19), so
     the mark seems to carry no meaning.
P14. Answering O4: the Expected panel shows what the position is given
     (P15), such as the parameter or field at an argument, the
     matching entry at a tuple's element and the goal at a `qed`'s
     expression. D22's indication appears where nothing is given and,
     extending D22, for a tuple `let` binder with neither a type nor an
     `is` clause.
P15. What a position gives (§8): a function body its returns, a branch
     body the annotation, a `qed`'s expression the goal, a tuple
     `let`'s right-hand side its binders (a binder with neither a type
     nor an `is` clause taking any result), a block's final expression
     what the block is given, an argument its parameter or field, and a
     tuple's element the matching entry. An expression's results are
     checked against what it is given as arguments are against
     parameters, so a block's results are checked in the block's
     scope, with its facts in force. A tuple `let` binder's type or
     `is` clause is therefore checked where the result it names is
     produced, whether or not the other binders carry one. A `qed`'s
     expression being given the goal goes beyond D42, which settles
     only whether `_` stands for the goal there.
P16. Taint is stated per result and per tuple `let` binder, rather than
     per entry, since under D37 one entry can be both a tainted and an
     untainted result: in `{ let IsZeroHere() = s; n }`, with `n` a
     parameter and `s : IsZero(n)` tainted, D10's pattern-`let` rule
     seems meant to taint the block's result, which is `n`'s entry,
     there and not wherever `n` is used. In detail:
     - D10's "tainted when anything it is built from is" is read per
       result: a tuple's or block's result from the matching element or
       final-expression result, a match's from the scrutinee and the
       branches' matching results. So in
       `let (a, b) = (Zero(), sorry(_ : Nat()));` only `b` is tainted,
       D11 being read as covering a tuple `let` whose results are all
       tainted. The simpler alternative is to taint all of a tuple's
       or match's results together, as for a call.
     - The use of a tuple `let` binder is tainted when the binder is,
       and taint within a group is computed from "everything starts
       untainted" until nothing more becomes tainted.
     - D24 is stated generally: a function whose body binds a tainted
       result that reaches none of its results is untainted, and a call
       to it is tainted only by its arguments.
     - D27's "acts on the rest of the program as D10's pattern-`let`
       rule acts on the rest of a block" becomes: a tainted top-level
       pattern `let` taints every result of the top-level statements
       after it.
     - D13's "`T` mentions no tainted entry" becomes "the results of
       `T` and of `e` are untainted".
     - D28 becomes: every expression whose results are all tainted is
       removed, with everything in it, so a match only some of whose
       results are tainted still runs, for the others.
P17. Checking stops at the first error, which the interface shows where
     it occurs.
P18. Names (§2): a declaration, not only a binder, is not allowed to
     reuse a name in scope other than its own (so `Type` stays
     reserved); a telescope, a pattern or a tuple `let` is not allowed
     to introduce one name twice; and a function's own name is in scope
     in its telescopes as well as its body, so `fn f(f : Nat())` is an
     error rather than two meanings of `f` in the body.
P19. §19 gives a grammar of phase 1, summarizing the syntax that §1,
     §5, §6 and §8 to §12 describe. Where the prose is silent, it
     rejects an empty `mutual` block.
P20. Smaller points, some of which seem to follow from DESIGN.md as it
     stood:
     - §7: forcing is stated for a value constructor at a match or
       pattern `let`, and failing refutes the value constructor rather
       than "the branch"; the checker also knows which value
       constructor a `comptime` run produced.
     - §8: a tuple `let`'s binders are in scope after the `let`, to the
       end of the enclosing block, or of the program; §12: `sorry`'s
       telescope's names are in scope only in its later entries. So
       `let x = sorry(x : Nat());` is allowed, and P18 is what rejects
       `let (x, x) = e;`.
     - §9: only a call within its group has marks; a mark elsewhere is
       an error.
     - §10: each branch is for a value constructor of the scrutinee's
       data type constructor, and gives the fresh entries its fields
       are opened to a name or `_`; the sentence on a later phase
       allowing a top-level pattern `let` goes with the ban.
     - §11: a `comptime` pattern `let`'s `C` must survive forcing, and
       the other value constructors need not be refuted; how a match
       and a pattern `let` evaluate; what a value is; that a failed
       `comptime` pattern `let` shows a value; why the reflection
       example needs `comptime`.
     - §13: `inspect;` reports beside the statement.
     - §3, §6: "tuple `let`" where only a tuple `let`'s binders are
       meant.
     - §17: the review status.

P21. Details of function goals (§12), proposed with them and not
     separately approved:
     `subterm` marks are not part of a signature, so the goal states
     none and `f` is allowed any marking; and the goal's telescopes
     are allowed `_` names, since names do not matter for the match.

## Open questions

O5. A block's results keep the types they were created with, and its
    facts end with it (§7). So after
    `let (t : Vec(A, n)) = { let VCons(_, _, _, r) = v; r };`, with
    `v : Vec(A, Succ(n))`, the binder's type is checked inside the
    block (P15) and passes, yet `t`, naming `r`'s entry (D37), has a
    type that mentions the pattern's fields rather than `A` and `n`.
    Is that intended, or should a block that is given something produce
    new entries typed by it, as a match's results are typed by its
    annotation?

## Pending edits

To SOUNDNESS.md: what D10 to D14 and D19 to D28 require there:
`comptime`, top-level evaluation of every `let`, part 7 (checking
terminates, now that checking runs code), stripping, the taint rules,
and that a goal proved in a program containing `sorry` is proved. This
includes checking that nothing left after stripping needs a removed
value, which D10 and D27 are meant to ensure; nothing beyond one
review has checked it. If approved, P15 and P16 also bear on it: where
results are checked, taint per result, and a match only some of whose
results are tainted.
