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

None at present.

## Proposals, not approved

DESIGN.md does not apply P3.

P3. The Scope panel shows whether each entry is tainted.

## Open questions

O5. A block's results keep the types they were created with, and its
    facts end with it (§7). So after
    `let (t : Vec(A, n)) = { let VCons(_, _, _, r) = v; r };`, with
    `v : Vec(A, Succ(n))`, the binder's type is checked inside the
    block (§8) and passes, yet `t`, naming `r`'s entry (§8), has a
    type that mentions the pattern's fields rather than `A` and `n`.
    Is that intended, or should a block that is given something produce
    new entries typed by it, as a match's results are typed by its
    annotation?

## Pending edits

To SOUNDNESS.md: what §8, §11 and §12 require there: `comptime`,
top-level evaluation of every `let`, part 7 (checking terminates, now
that checking runs code), what taint removes, the taint rules, where
results are checked, a match only some of whose results are tainted,
and that a goal proved in a program containing `sorry` is proved. This
includes checking that nothing left after taint's removal needs a
removed value; nothing beyond one review has checked it.
