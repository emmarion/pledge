# To do

Work that seems to remain after `_` for an argument or inside a type
(DESIGN.md §20) and no type being evaluated (§11). Items are cited by
number; numbers are never reused.

## 1. The tutorial introduces `_` only in phase 2

`_` for an argument of type `Type()` and inside a type works in
phase 1, but the tutorial first shows a `_` argument on the phase 2
page "_ for erased arguments". A phase 1 learner may never see
`VCons(_, Zero(), x, VNil(_))` or `let v : Vec(Nat(), _) = …`. This
could be a short phase 1 page, or a paragraph on an existing page with
the phase 2 page retitled.

## 2. SOUNDNESS.md has not been revisited

Its prose argument predates §11's rule that no type is evaluated: claim
(P), that every evaluation produces values of the types, would need to
cover the blank that stands for a type. It also says nothing about
solving a `_`.

## 3. The likely bugs in notes/BUGS.md

Both are deferred by the owner.

## 4. Lean coverage of `_`

The Lean theorems cover only programs with no `_` for an argument or
inside a type. One way to extend them, proposed but not decided, is
for the checker to re-check the program with each `_` written out as
its solution, so that the existing theorems apply without any proof
about the solver. This seems the largest item, and the most proof-heavy.
