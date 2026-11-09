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

D53. A program that does not parse is checked up to the declaration or
     statement that fails to parse. Its error is the first in text
     order: an error in checking what parsed, and otherwise the syntax
     error.
D54. The interface's report on the `qed` tells a `qed` that checking
     did not reach from one that does not check. Whether the text has
     a `qed`, and whether it has a `goal`, is read off the text, as the
     presence of `sorry` is, so the report stands when the text does
     not parse.
D55. At a position inside a declaration, Scope lists the entries
     created in that declaration; top-level bindings are listed under
     Globals. At a top-level position Scope lists the top-level
     entries. An entry with no name is listed only when the type or
     `is` rule of a listed entry, or an Expected entry, mentions it.
D56. A refutation's derivation lists the failing equation, the
     equations it descends from, and the equation that gave each rule
     a listed equation was rewritten by, when the same forcing gave
     that rule.

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
