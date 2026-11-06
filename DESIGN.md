# Pledge

Pledge is a language for teaching restricted dependent types. It runs in
a web browser and is implemented in TypeScript. Its main interface shows
what the type checker knows at any point of a program (§13).

The language comes in phases, each a superset of the one before, and a
later phase's features can be switched on or off. This file describes
phase 1; §16 lists what is planned beyond it.

Soundness is essential: no program may prove `False`. Pledge has
`Type : Type` and no positivity requirement, and avoids universes,
hierarchies and positivity by other restrictions: types never contain
function calls (§3), functions are not first class (§4), and
termination comes from definition order and structural decrease, not
from types (§9). SOUNDNESS.md argues that these suffice.

Pledge is loosely based on [Sleight](https://github.com/emmarion/sleight)
and shares none of its code.

## 1. Syntax

Source text is ASCII. `--` starts a comment that runs to the end of the
line. Blocks are delimited by braces; layout is not significant.
Statements end with `;`.

A binder is written `name : T`, or `name is e` (§6). A telescope is a
parenthesized, comma-separated list of binders, each of which may refer
to the binders before it. `_` as a binder name binds nothing.

Every application is saturated and written `f(a1, ..., an)`; there is no
currying. A nullary constructor is written without parentheses.

```
data Nat : Type {
  Zero : Nat
  Succ(pred : Nat) : Nat
}

data Vec(A : Type, n : Nat) : Type {
  VNil(A : Type) : Vec(A, Zero)
  VCons(A : Type, n : Nat, head : A, rest : Vec(A, n)) : Vec(A, Succ(n))
}

fn vhead(A : Type, n : Nat, v : Vec(A, Succ(n))) -> (x : A) {
  let-match VCons(_, _, hd, _) = v;
  hd
}
```

## 2. Names

There is one namespace, and any name may be shadowed. A name refers to
a value, a function, a type constructor or a value constructor. Only a
value may be passed, returned, bound or stored.

## 3. Types

A type is built from:

1. variables;
2. `Type`;
3. applications of a type constructor;
4. applications of a value constructor.

A type never contains a function call. Type checking is: canonicalize
both sides by the `is` facts in force (§7), then compare for identity.

`Type : Type`. There is no universe hierarchy and no positivity
requirement. Pattern matching assumes uniqueness of identity proofs
(Axiom K).

## 4. First-class values

Types are first class: a value of type `Type` may be passed, returned,
bound with `let` and stored in a constructor field. A value of type
`Type` cannot be matched on.

Functions, type constructors and value constructors are not first
class. They are applied, never passed or stored.

## 5. Data types

```
data T(params) : Type {
  C(fields) : T(args)
  ...
}
```

Each value constructor declares its own telescope of fields, and returns
`T` applied to one argument per parameter of `T`. The arguments may
refer to the constructor's fields. The parameters of `T` are in scope
only in its own telescope: a constructor that constrains an index
declares its own field for it. A data type may have no constructors.
Mutually recursive data types are declared together in a `mutual`
block.

## 6. `is`

Wherever a variable is introduced, `x is e` may be written in place of
`x : T`: in function parameters and returns, constructor fields,
type-constructor parameters, match annotations and `let` binders. The
type of `x` is then the type of `e`, and `e` must be in the grammar of
§3. An argument supplied for an `is` parameter or field, or a result
supplied for an `is` return, must canonicalize to the same term as `e`.

A `let` binder may carry a type, an `is` clause, or neither. A type or
`is` clause written on a `let` binder is checked for identity against
what the checker infers, so `let y is Succ(n) = e;` asserts a fact the
checker must already know.

## 7. What the checker knows

The checker keeps a scope of entries. Each entry has a type and may have
an `is` rule, a rewrite from the entry to a term of §3's grammar.
Canonicalizing a term rewrites it by these rules to a fixed point.

The checker knows only what it can infer from the text. `let x =
Cons(Nat, Zero, Nil(Nat));` gives `x is Cons(Nat, Zero, Nil(Nat))`. The
results of a function call are new entries known only by their types,
except where the function's return telescope states an `is` (§6).

Every constructor application and every result of a call is an entry of
its own, usually anonymous. The interface shows an anonymous entry by a
marker giving what kind of entry it is and where it was created.

**Forcing.** Entering a match branch equates the scrutinee with the
branch's constructor applied to fresh fields, and the scrutinee's type
with that application's type. This adds `is` facts, recursing through
matching applications. When two variables are equated, the newer
becomes an alias of the older. The facts last until the branch ends.
As in Sleight, forcing fails, refuting the branch, when:

1. a variable is equated with a term containing it;
2. two applications of different constructors are equated;
3. a variable is equated with a term whose type cannot be equated with
   the variable's.

## 8. Functions

```
fn name(params) -> (returns) { body }
```

Functions are defined only at the top level. There are no nested
functions and no closures. Mutually recursive functions are written
together in a `mutual` block, their **group**; a function outside any
`mutual` block is a group of its own.

A function returns zero or more values. The return telescope may
depend on the parameters and on earlier returns. A body is a sequence of
statements followed by a final expression; `(a, b)` produces several
values, and `let (q, r) = divmod(n, d);` binds them.

## 9. Termination

A body may call:

- any function of an earlier group, with no annotation;
- a function of its own group, under the decrease below.

Parameters may be marked `subterm`, including `is` parameters
(`subterm m is Succ(n)`). A function's `subterm` parameters are its
**slots**, numbered 1, 2, ... in order. A call within the group marks,
for some slot `k`, the argument for the callee's `k`-th `subterm`
parameter `subterm e`, and the argument for each of its earlier
`subterm` parameters `same e`; every other argument is unmarked. The
call is accepted when the caller has slots 1 to `k` and:

- after canonicalization, `e` at slot `k` is a strict subterm of the
  caller's own `k`-th `subterm` parameter;
- each `same` argument is canonically identical to the caller's
  `subterm` parameter at its slot.

```
fn ack(subterm m : Nat, subterm n : Nat) -> (r : Nat) {
  match m : (r : Nat) {
    Zero => Succ(n)
    Succ(m1) => match n : (r : Nat) {
      Zero => ack(subterm m1, Succ(Zero))
      Succ(n1) => ack(subterm m1, ack(same m, subterm n1))
    }
  }
}
```

Code at the top level calls any function, with no annotation.

## 10. Matching

```
match e : (telescope) {
  C(x1, ..., xn) => body
  ...
}
```

The annotation is mandatory; it is the telescope the match produces, so
a match may return several values. `_` in its place reuses the
telescope the position expects. A branch binds one name per field of
its constructor. Every constructor has at most one branch. A
constructor is **refuted** when its forcing fails (§7); a refuted
constructor has no branch, and every other constructor has one. A
branch for a refuted constructor is an error. Refutation comes only
from forcing, never from a proof. A match on a value of a type with no
constructors has no branches.

`let-match C(x1, ..., xn) = e;` is a statement. Exactly one constructor
of `e`'s type may survive forcing, and it must be `C`; its fields and
facts stay in scope for the rest of the enclosing body.

## 11. Compile time

A program has no run-time stage: code is evaluated only at compile
time, and only when asked to, by `print` (§12) and two top-level
statements:

- `comptime let x = e;` evaluates `e` during checking. The checker
  knows of `x` exactly what it would know after `let x = e;`.
- `comptime let-match C(x1, ..., xn) = e;` evaluates `e` during
  checking and requires the result to be headed by `C`; otherwise it is
  an error showing the value. It is then checked as a `let-match`, except
  that the run, not forcing, rules out the other constructors.

This is how a proof by reflection is written:

```
comptime let-match Some(_, p) = decideEven(N);
```

A `comptime` expression may refer only to functions, constructors and
earlier `comptime` bindings.

## 12. `sorry`, `print`, `goal` and `qed`

`sorry` is an expression of any type, and checking goes on past it as
past any other expression. The interface reports whether a program
contains `sorry` anywhere. Once an evaluation reaches `sorry`, the
program evaluates nothing more: from there on, every `print` shows
`sorry` and every `comptime let-match` is accepted without its head
check.

`print e;` is a top-level statement that evaluates `e` at compile time
and shows its value, as a tree of constructor applications, beside the
statement. Like a `comptime` expression, `e` may refer only to
functions, constructors and `comptime` bindings.

`goal T;` sets the program's goal, a type. `qed e;` checks `e` against
it. Each is a top-level statement and appears at most once in a program,
`qed` after `goal`. The goal is proved when the `qed` checks and the
program contains no `sorry`. A `qed` that checks in a program containing
`sorry` proves nothing; the interface reports that the `qed` checks
and that the program contains `sorry`.

A tutorial page shows one or more read-only boxes of source above the
learner's editable box, and checks them all as one program, in order.
Whether the learner's box must hold the `qed` is up to the page.

## 13. Seeing what the checker sees

At any position in a program, the interface shows:

- **Expected**: the telescope still to be produced there.
- **Termination**: the enclosing function's `subterm` parameters, in order,
  and the functions of its group.
- **Scope**: the local entries, each with its type and `is` rule, and,
  in phase 2, whether it is erased.
- **Refutations**, at a `match` or `let-match`: for each refuted
  constructor, separately, why its forcing fails.
- **Globals**, behind a switch: functions, data types and top-level
  bindings, each binding marked `comptime` or not.

Types and terms are shown canonicalized.

In the interface's interactive mode, a type or an expression typed in is
checked in the scope at the selected position, and its type and `is`
rule are shown, both as inferred and canonicalized.

The interface lists functions apart from values because they are not
first class (§4); they are still in the one namespace (§2).

The statement `inspect;` reports the same information as text.

## 14. Implementation

Checking produces, for the code it evaluates, a separate syntax tree
with erased positions removed, and a tree-walking interpreter evaluates
that tree.

## 15. Not in phase 1

Every binder has multiplicity `many`; no multiplicity is written. There
are no literals, strings, characters or input. `_` is inferred only in
place of a match annotation.

Pledge has no uniqueness, no `at` and no coercions, in any phase.

## 16. Later phases

Phase 2 adds erasure. Every binder has a multiplicity, `many` or
`erased`: function parameters and returns, constructor fields, the
binders of every kind of `let`, and match annotation entries.
A binder whose type is `Type` is erased unless written `many`; any
other binder is `many` unless written `erased`.
Type-constructor arguments are always erased. Constructors themselves
are never erased, and every value carries its constructor's tag.

An erased name may be used only in an erased position: a type, an
argument for an erased parameter or field, the result for an erased
return or binder, and everything inside these. A call whose results are
all erased takes any arguments. Evaluation skips erased positions, and
`print` shows an erased field as `_`.

`match erased e : (...)` takes its scrutinee erased; a match without a
multiplicity is `many`. A destructure binds a field erased when the
field or the match is erased, and `many` otherwise. An erased match with
a `many` annotation entry has at most one branch.

`_` then also stands for erased arguments, solved by unification.

Phase 3 is to be designed later. It will allow creating an executable,
a program with input and output.
