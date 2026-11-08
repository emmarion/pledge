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

D1. A statement in a block is a `let` (plain, tuple or pattern) or
    `inspect;`. `e;` is not a statement.
D2. `(a)` is a one-element tuple. Each element of a tuple produces one
    value.
D3. `_` in place of a telescope can stand for any telescope, including
    one mixing types and `is` entries, so it is allowed in a `let`
    whose binders carry `is` clauses. This seems consistent with §6:
    the binder is checked against what the checker infers, which is
    then the telescope itself.
D5. A `mutual` block is allowed to hold functions that do not call
    each other.
D6. Each element of a tuple is checked against the matching entry of
    the tuple's telescope, so `(Zero(), sorry : _)` is accepted where
    a two-entry telescope is given.
D7. `qed sorry : _;` is allowed: the goal is the telescope there.
D8. The interface reports whether the program contains `sorry`
    anywhere, as well as whether the `qed` checks and whether the goal
    is proved.
D9. `sorry` takes a telescope, written as a match annotation is:
    `sorry : (telescope)` produces one new entry per entry of the
    telescope, described by it, types and `is` rules alike.
    `sorry : _` stands for the given telescope.
D10. Taint is decided statically, from the text, without evaluation:
     - every result of `sorry` is tainted;
     - an application, tuple, block or match result is tainted when
       anything it is built from is, a match's scrutinee included;
     - a pattern `let` whose scrutinee is tainted taints every result
       of its block;
     - a function is tainted when a tainted entry reaches any of its
       results in its body (one bit per function);
     - all of a call's results are tainted when the function is tainted
       or any argument is;
     - in a scope, an entry is tainted when its type or `is` rule,
       canonicalized there, mentions a tainted entry;
     - nothing else is tainted; for recursion, everything starts
       untainted, with no special case for `mutual` groups.
D11. A tainted top-level plain or tuple `let` evaluates nothing, and
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
D17. No zero results in phase 1: a function has at least one return, a
     match annotation at least one entry, a tuple at least one element,
     and a `let` at least one binder. `()` is not an expression.
D18. Evaluation is eager: a call evaluates its arguments, in order,
     before its body, and a block evaluates its statements in order,
     then its final expression.
D19. Top-level statements are evaluated as soon as they are checked,
     every `let` included. Top-level statements have parity with a
     block's, mostly; `print` stays top-level only. `goal` and `qed`
     are evaluated like other top-level statements, and only `print`
     shows a value.
D20. A tuple `let` is allowed at the top level.
D21. `inspect;` is allowed at the top level.
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

## Approved rules awaiting wording

R1. A block is zero or more statements, then a final expression. A
    statement in a block is a `let` or `inspect;`.
R2. A tuple of `n >= 1` elements produces `n` values. A call produces
    one value per return, a match one per annotation entry, and a block
    what its final expression produces. Anything else produces one.
R3. A function body must produce one value per return, a branch body
    one per annotation entry, and a `let`'s right-hand side one per
    binder. Anywhere else, an expression must produce one value.
R4. Functions, annotations and `let`s have at least one return, entry
    or binder.

## Proposals, not approved

P1. Placeholders: evaluating `sorry` gives a placeholder; a match on
    one evaluates no branch and gives placeholders; a pattern `let` on
    one skips the rest of its block and gives placeholders. To be
    withdrawn if P7 is approved.
P2. §7 says a pattern `let`'s facts last "to the end of the enclosing
    body", and §10 says "block". Proposal: "block" in both.
P3. The Scope panel shows whether each entry is tainted.
P4. R2 and R4 extended for D9: `sorry` produces one value per entry of
    its telescope, which has at least one entry.
P5. Where `_` is allowed in place of a telescope (D15), and what it
    stands for:
    - a function body: the return telescope;
    - a branch body: the annotation;
    - a block's final expression, or a tuple element, when the block or
      tuple is itself in one of these positions: that position's
      telescope, or its matching entry;
    - the `i`-th argument of a call or application: the `i`-th
      parameter or field;
    - the right-hand side of a `let` whose binders all carry a type or
      an `is` clause: those binders;
    - a `qed`: the goal.

    For tuple elements and arguments, the earlier entries stand for the
    earlier elements' or arguments' entries. Every telescope is read
    with the facts in force at the position. Anywhere else, `_` is an
    error. The Expected panel (D22) would show a telescope exactly at
    these positions.
P6. A plain top-level `let C(x1, ..., xn) = e;` is checked as in a
    block, by forcing (§10), by D19's parity. The owner has not
    confirmed this.
P7. How stripping (D26) works: before anything is evaluated, every
    tainted entry is stripped, together with the computation that would
    produce it, as phase 2 strips erased positions (§14, §16), so
    evaluation never reaches a `sorry`.
P8. An amendment to D10: a `let` binder whose right-hand side's result
    is tainted is tainted, whatever its canonical type or `is` rule.
P9. An amendment to D11: after a tainted top-level pattern `let`, plain
    or `comptime`, nothing evaluates and no `qed` proves the goal.
P10. §14 says erased positions exist from phase 2 on.

## Open questions

O1. Is P7, with P8 and P9, how the owner wants stripping to work?
    Stripping seems safe only if nothing untainted is computed from a
    tainted result. A review found three ways D10 and D11 as they stand
    seem to allow that; P8 and P9 are meant to close them, but this has
    not been checked beyond that review:
    1. Canonicalization can hide taint. After `let x = sorry :
       (x is Zero());`, `let y = x;` gives `y is x`, which canonicalizes
       to `y is Zero()`, so `y` would be untainted, and `print y;`
       would read a stripped value. (P8)
    2. Pattern-`let` fields. D10 does not taint the fields of a pattern
       `let` whose scrutinee is tainted. In a block this seems harmless,
       since every result of the block is tainted; at the top level,
       after a tainted `let Succ(m) = s;`, `print Succ(m);` would read a
       stripped value. (P9)
    3. Forcing. A tainted top-level pattern `let` can force a false
       `is` rule onto an untainted entry. With `m : Nat()` untainted,
       `let Refl(_, _) = s;` on a tainted `s : Eq(Nat(), m,
       Succ(Zero()))` forces `m is Succ(Zero())`, and a later untainted
       `let VCons(...) = w;` on `w : Vec(Nat(), m)` is accepted but
       fails at run time if `m` is really `Zero()`. (P9)

O2. §13's Globals mark each top-level binding "`comptime` or not". Now
    that every `let` is evaluated (D19) and `comptime` is written only
    on a pattern `let` (D23), does the mark stay, and what does it mean?

## Pending edits

To DESIGN.md:

- §12: replace `sorry` "of any type" and the "once an evaluation
  reaches `sorry`" rule with D9 to D14 and D24, D26.
- §8: blocks and value counts from R1 to R4 (with P4 if approved), D2,
  D6 and D17; "returns zero or more values" becomes "one or more".
- §10: the `_` sentence from D15 (with P5 if approved); §15's "`_` is
  inferred only in place of a match annotation" becomes "only in place
  of a match annotation or `sorry`'s telescope".
- §11: D18, D19, D23; the `comptime let x = e;` form and the rule on
  what a `comptime` expression is allowed to refer to go.
- §12: `print`'s restriction to `comptime` bindings goes (D19).
- §10 and §15: the bans on a top-level pattern `let` go (D19, D23).
- §13: D21, D22, and O2's answer.
- §5: `data` declarations are top-level only, which follows from R1, as
  §8 says of functions.
- §7: P2, if approved. §14: P10, if approved.

To SOUNDNESS.md: what D19 to D26 require there: `comptime`, top-level
evaluation of every `let`, part 7 (checking terminates, now that
checking runs code), and stripping.
