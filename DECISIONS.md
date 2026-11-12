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
D60. Tentatively: the global entries come right after Local entries, and the
     Data declarations and Functions last.
D61. Tentatively: the global entries are in creation order.

## Approved rules awaiting wording

D66. A program with a `_` for an argument or inside a type (§20) checks
     as if each `_` were replaced by a written term, except that the
     term is allowed to refer to entries that have no name. A `_` is
     solved only when its solution is unique up to canonicalization.
D67. §16's restriction, that an erased name is allowed only in an
     erased position, does not apply to an entry whose type is
     `Type()`.
D68. Where canonicalization makes several terms identical, a `_` is
     the untainted one whenever one of them is untainted.
D69. §20 is to change for a tuple `let` whose binders contain a `_`:
     its right-hand side is checked first, and then each binder
     against the result it names.
D70. A `_` in a tuple `let` binder is allowed to stand for the result
     a later binder names, as in
     `let (v : Vec(Nat(), _), n : Nat()) = (VNil(Nat()), Zero());`.
D71. D66's "unique up to canonicalization" is judged with the facts in
     force at the end of what the `_` must be solved by (§20).

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
     Data declarations and Functions show signatures as written.
     Should §13 say so?

## Pending edits

None at present.
