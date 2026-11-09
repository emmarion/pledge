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

D3. `_` in place of a telescope can stand for any telescope, including
    one mixing types and `is` entries, so it is allowed in a `let`
    whose binders carry `is` clauses. This seems consistent with §6:
    the binder is checked against what the checker infers, which is
    then the telescope itself.
D5. A `mutual` block is allowed to hold functions that do not call
    each other.
D6. Each element of a tuple is checked against the matching entry of
    the tuple's telescope. (`(Zero(), sorry(_))`, once given here as
    accepted, seems ruled out by D41; the owner has not yet confirmed
    this.)
D8. The interface reports whether the program contains `sorry`
    anywhere, as well as whether the `qed` checks and whether the goal
    is proved.
D9. `sorry` takes a telescope, written `sorry(telescope)`, as a
    function's parameters are, so `sorry(x is Zero())`. It produces
    one new entry per entry of the telescope, described by it, types
    and `is` rules alike. `sorry(_)` stands for the given telescope.
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
D12. `print e;` shows `sorry`, and evaluates nothing, when `e`'s result
     is tainted.
D13. `goal T;` is checked in the scope where it is written. The goal is
     proved when the `qed` checks, `T` mentions no tainted entry, `e`'s
     result is untainted, and no tainted top-level `comptime` pattern
     `let` comes before the `qed`.
D14. Any use of `sorry` is unsound. Taint only tracks what relies on
     one.
D15. DESIGN.md does not use "expects" or "expected telescope". Where a
     telescope is given is stated by listing the positions.
D16. DESIGN.md never says bare "constructor", and avoids "may" where
     permission and possibility could be confused.
D18. Evaluation is eager: a call evaluates its arguments, in order,
     before its body, and a block evaluates its statements in order,
     then its final expression.
D19. Top-level statements are evaluated as soon as they are checked,
     every `let` included. Top-level statements have parity with a
     block's, mostly; `print` stays top-level only. `goal` and `qed`
     are evaluated like other top-level statements, and only `print`
     shows a value.
D20. A tuple `let` is allowed at the top level.
D22. Where a position has no telescope to produce, the Expected panel
     shows an explicit indication that none has been determined there.
D23. `comptime let C(x1, ..., xn) = e;` is allowed at the top level,
     beside plain `let`. It evaluates `e` and asserts that the result
     is headed by `C`. `comptime` is written only on a pattern `let`;
     there is no `comptime let x = e;`.
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
D32. A `comptime` pattern `let` is top-level only, for now, since that
     simplifies things.
D33. A plain top-level pattern `let` is checked as in a block, by
     forcing: exactly one value constructor of the scrutinee's type
     survives forcing, and it is the written one. The plain and
     `comptime` forms differ only in what rules out the other value
     constructors: forcing, or the run.
D35. For D16's "may": DESIGN.md says "is allowed to" for permission and
     "can" for possibility, as in "no program can prove `False`",
     applied to each section as the section-by-section pass reaches it.
D37. A tuple `let` binder names the entry produced for it; it
     adds no entry and no rule. After `let y = x;`, `x` and `y` are two
     names for one entry, and the Scope panel (§13) shows both names on
     it.
D40. In phase 1, `_` is not allowed at an argument of a call or
     application. The owner sees no
     sensible way to support it before phase 2; if it comes, it would
     probably work back from later arguments or from what the result
     must be, except perhaps for an `is` parameter.
D41. In phase 1, `_` stands only for an entire telescope, never for one
     entry of it; so not at a tuple's element or at an argument.
D42. Whether a `qed`'s expression gives the goal as the telescope that
     `_` stands for, so whether `qed sorry(_);` is allowed, is an
     implementation choice, and DESIGN.md says so. (This replaces D7,
     which said it was allowed.)

## Approved rules awaiting wording

None at present.

## Proposals, not approved

P3. The Scope panel shows whether each entry is tainted.
P11. The positions where a whole telescope is given, so where `_` is
     allowed under D41: a function body (the returns), a branch body
     (the annotation), a block's final expression at one of these
     positions, the right-hand side of a tuple `let` whose binders all
     carry a type or an `is` clause (those binders), and, as an
     implementation choice (D42), a `qed`'s expression (the goal).
P10. §14 says erased positions exist from phase 2 on.

## Open questions

O2. §13's Globals mark each top-level binding "`comptime` or not". Now
    that every `let` is evaluated (D19) and `comptime` is written only
    on a pattern `let` (D23), does the mark stay, and what does it mean?

O4. Should the Expected panel (D22) show the telescope at an argument
    of a call or application, which the checker knows since arguments
    are checked in order, although `_` is not allowed there (D40)?

## Pending edits

To DESIGN.md:

- §12: replace `sorry` "of any type" and the "once an evaluation
  reaches `sorry`" rule with D9 to D14, D24 and D26 to D28.
- Where §10 says a binder stands for an entry: its wording against
  §3's opening and instantiating.
- §8: D6.
- §10: the `_` sentence from D15 and D41 (with P11 if approved); §15's "`_` is
  inferred only in place of a match annotation" becomes "only in place
  of a match annotation or `sorry`'s telescope".
- §11: D18, D19, D23; the `comptime let x = e;` form and the rule on
  what a `comptime` expression is allowed to refer to go.
- §12: `print`'s restriction to `comptime` bindings goes (D19).
- §10 and §15: the bans on a top-level pattern `let` go (D19, D23).
- §13: D22, D37's Scope panel, and O2's answer.
- §14: P10, if approved; D28's likeness to how
  phase 2 removes erased positions, if approved.
  D42, landing with the §10 `_` sentence and the §12 `sorry` edit.

To SOUNDNESS.md: what D10 to D14 and D19 to D28 require there:
`comptime`, top-level evaluation of every `let`, part 7 (checking
terminates, now that checking runs code), stripping, the taint rules,
and that a goal proved in a program containing `sorry` is proved. This
includes checking that nothing left after stripping needs a removed
value, which D10 and D27 are meant to ensure; nothing beyond one
review has checked it.
