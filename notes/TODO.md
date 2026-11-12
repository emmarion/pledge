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

## 2. SOUNDNESS.md's argument has not been revisited

Its prose argument predates §11's rule that no type is evaluated: claim
(P), that every evaluation produces values of the types, would need to
cover the blank that stands for a type. It also says nothing about
solving a `_`.
