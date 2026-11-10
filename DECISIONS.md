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

D15. DESIGN.md does not use "expects" or "expected telescope". Where a
     telescope is given is stated by listing the positions.
D16. DESIGN.md never says bare "constructor", and avoids "may" where
     permission and possibility could be confused.
D35. For D16's "may": DESIGN.md says "is allowed to" for permission and
     "can" for possibility, as in "no program can prove `False`",
     applied to each section as the section-by-section pass reaches it.

## Approved rules awaiting wording

D36. `_` is allowed only as an erased argument, as an argument whose
     type is `Type()`, or anywhere inside a type; it never stands for
     any other `many` argument. Being allowed is necessary, not
     sufficient: each `_` must also be solved, by rules along the lines
     of Sleight's (its DESIGN.md §50). DESIGN.md §10, §13, §15, §16 and
     §19 still describe `_` as it was before this decision.
     ASSUMPTIONS.md item 51 lists how the code reads it.
D37. A type has one run-time representation, equivalent to the unit
     type: no type is evaluated, `print` shows every type as `_`, and a
     `_` for a `many` argument of type `Type()` is allowed to be solved
     from erased values. DESIGN.md §11, §12 and §16 still describe
     values and `print` as they were before this decision.
     ASSUMPTIONS.md items 49 and 51 list how the code reads it.

## Proposals, not approved

None at present.

## Open questions

None at present.

## Pending edits

None at present.
