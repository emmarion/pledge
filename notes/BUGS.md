# Likely bugs

Behaviour of both checkers that seems to disagree with DESIGN.md, found
but not yet fixed. Each item is cited by number; numbers are never
reused. Each is a candidate, not confirmed by the owner, and may turn
out to be what DESIGN.md means.

## 1. A `_` in a tuple `let` annotation typed by an earlier binder

```
let (A : Type(), x : A, p : Eq(A, x, _)) = (Nat(), Zero(), Refl(Nat(), Zero()));
```

is rejected with "this `_` would be `Zero()`, of type `Nat()`, and it
must have type" an entry the reader cannot see, and checks with `x` in
place of the `_`. The `_` seems to be typed by the entry the binder
`A` is first opened to, which is never identified with the result
bound to `A`.

DESIGN.md §20 says a `_` is solved by unification to whatever makes
the two sides identical, which would seem to accept this.

## 2. A `_` solved to an earlier value that a later argument refines

```
data IsS(n : Nat()) : Type() {
  MkIsS(erased m : Nat()) : IsS(Succ(m));
}
fn f(erased n : Nat(), q : IsS(n), k : Nat()) -> (r : Nat()) {
  k
}
fn g(k : Nat(), z : IsS(k)) -> (r : Nat()) {
  f(_, z, { let MkIsS(a) = z; k })
}
```

is rejected with "which mentions what is produced only after it", and
checks with `k` in place of the `_`. The `_` is solved to `k`, which
exists before it, but the test for that is made on the canonical form,
after the later pattern `let` has made `k` canonicalize to `Succ(a)`.

Whether this is a bug depends on whether §20's "mention only entries
that exist before the `_`" is meant of the term before or after
canonicalization, which DESIGN.md does not seem to settle.
