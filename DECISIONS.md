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

D50. A scope is tainted when a fact forced from a tainted scrutinee is
     in force in it: each branch of a match on a tainted scrutinee,
     and, for a pattern `let`, the reach of its facts (§7). Every
     result produced in a tainted scope is tainted, so a function
     written in one is tainted. A match's result is also tainted when
     its scrutinee's is, which covers a match with no branches.
D51. A name is tainted when it is a tuple `let` binder bound to a
     tainted result. A use of a name is tainted when the name is or
     the scope is.
D52. The Scope panel says when the scope is tainted, linking to the
     scrutinee responsible, and tags each tainted name; an entry gets
     no tag of its own. The hover tip tags a tainted name the same way.

## Proposals, not approved

None at present.

## Open questions

None at present.

## Pending edits

To SOUNDNESS.md: what §8 and §12 require there: what taint removes,
the taint rules, where results are checked, a match only some of whose
results are tainted, and that a goal proved in a program containing
`sorry` is proved. This includes checking that nothing left after
taint's removal needs a removed value; nothing beyond one review has
checked it.
