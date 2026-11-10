# Wish list

Limitations of the current checker that are not bugs against DESIGN.md
but that would be nice to lift. Each item is cited by number; numbers
are never reused (CLAUDE.md rule 15).

## 4. A `_` in a tuple `let` annotation typed by an earlier binder

```
let (A : Type(), x : A, p : Eq(A, x, _)) = (Nat(), Zero(), Refl(Nat(), Zero()));
```

is rejected with "this `_` would be `Zero()`, of type `Nat()`, and it
must have type" an entry the reader cannot see, and checks with `x` in
place of the `_`. The `_` seems to be typed by the entry the binder
`A` is first opened to, which is never identified with the result
bound to `A`.

## 5. A `_` solved to an earlier value that a later argument refines

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
