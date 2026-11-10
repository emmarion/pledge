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
D45. Some open questions will probably go into DESIGN.md as explicit
     TBDs; which ones is decided item by item.
D59. Tentatively: the two parts are called "Global entries" and
     "Declarations", and Scope's message at the top level (§13) points
     to "Global entries".
D60. Tentatively: the global entries come right after Scope, and the
     functions and type constructors last, where the Globals were.
D61. Tentatively: the global entries are in creation order.

## Approved rules awaiting wording

None at present.

## Proposals, not approved

None at present.

## Open questions

D51. Should clicking a skeleton term, and the interactive mode, refer to
     the entries of unnamed applications by their markers? Those entries
     are not yet in the scope at that position. The owner does not know
     yet, and tentatively keeps them writing applications in place.
D53. Should hovering over a `by (n)` line in the dialog show the rule
     with its arrow, as the code now does?
D65. §13 says types and skeleton terms are shown canonicalized, but the
     declarations part of the Globals shows signatures as written.
     Should §13 say so?

## Pending edits

None at present.
