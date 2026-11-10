# Wish list

Limitations of the current checker that are not bugs against DESIGN.md
but that would be nice to lift. Each item is cited by number; numbers
are never reused (CLAUDE.md rule 15).

## 1. `_` whose given type depends on an earlier `_`

In an application, a `_` argument is not solved when its given type
mentions an earlier `_` of the same application, even when that earlier
`_` is itself determined by what the application is given. For example:

```
data Head(n : Nat()) : Type() {
  HeadSucc(erased m : Nat()) : Head(Succ(m));
}

data Wrap(n : Nat()) : Type() {
  W(erased n : Nat(), h : Head(n)) : Wrap(n);
}

fn f(n : Nat()) -> (erased w : Wrap(Succ(n))) {
  W(_, HeadSucc(_))
}
```

This is rejected with "this `_` cannot be inferred". As far as we can
tell, the given `Wrap(Succ(n))` determines the first `_` as `Succ(n)`,
so `HeadSucc(_)` would be given `Head(Succ(n))` and its `_` could be
`n`. Writing either `_` out (`W(Succ(n), HeadSucc(_))` or
`W(_, HeadSucc(n))`) checks. DESIGN.md §16 says only that `_` is
"solved by unification", which seems not to settle whether this case
should work.

The example programs `tests/example_sort.pledge` and
`tests/example_typesafety.pledge` write such arguments out.
