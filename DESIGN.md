# Pledge

Pledge is a language for teaching restricted dependent types. It runs in
a web browser and is implemented in TypeScript. Its main interface shows
what the type checker knows at any point of a program (§13).

The language comes in phases, each a superset of the one before. A
program is checked under one phase, chosen by the learner or by a
tutorial page (§12), with the features of that phase and of every
earlier one. This file describes phase 1; §16 lists what is planned
beyond it.

Soundness is essential: no program can prove `False`. Pledge has
`Type() : Type()`. In place of a universe hierarchy, it relies on three
restrictions: types never contain function calls (§3), functions are not
first class (§4), and termination comes from definition order and
structural decrease, not from types (§9). SOUNDNESS.md argues that
these suffice. In a program that contains `sorry`, soundness also
relies on taint (§12). Since functions are not first class, positivity does
not arise.

Pledge is loosely based on [Sleight](https://github.com/emmarion/sleight)
and shares none of its code. Sleight's design is described in its
[DESIGN.md](https://github.com/emmarion/sleight/blob/main/DESIGN.md).

## 1. Syntax

Source text is ASCII. `--` starts a comment that runs to the end of the
line. A name is a letter followed by any number of letters, digits and
`_`; names are case-sensitive. Keywords (§18) are written like names.
Blocks are delimited by braces; layout is not significant.
Statements, value-constructor declarations and match branches end with `;`.
A `;` is also allowed after a `}` that needs none, and a `;` is allowed to be repeated.

A binder is written `name : T`, or `name is e` (§6). A telescope is a
parenthesized, comma-separated list of binders. It is checked in the
scope where it is written, with the facts in force there (§7), extended
by its own earlier binders and, for a return telescope, by the
parameters (§8). So each binder is allowed to refer to any entry in
scope there, a top-level one included, and to the binders before it.
`_` is allowed as the name of any binder, a return's included; it makes
the binder, and every entry it is opened to, anonymous (§7).

Every application is saturated and written `f(a1, ..., an)`; there is no
currying. A nullary application is written `f()`, so `Nat()` and
`Zero()`.

```
data Nat() : Type() {
  Zero() : Nat();
  Succ(pred : Nat()) : Nat();
}

data Vec(A : Type(), n : Nat()) : Type() {
  VNil(A : Type()) : Vec(A, Zero());
  VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));
}

fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  let VCons(_, _, hd, _) = v;
  hd
}
```

The parameters of a type constructor are in scope only in its own
telescope (§5), so `VNil` and `VCons` each declare their own `A`.

## 2. Names

There is one namespace, and no name is allowed to be shadowed: a binder
is not allowed to reuse a name that is in scope where it is written, or
a keyword. A name
refers to a value, a function, a type constructor or a value
constructor. `Type` is a built-in type constructor with no parameters,
and not a data type constructor (§5); `Type()` is the type of every
type, itself included (§3, §4). Only a value is allowed to be passed,
returned, bound or stored.

Names come into scope in the order they are written. A function's own
name is in scope in its body, and every function a `mutual` block
declares is in scope throughout the block. §5 says where the names a
`data` declaration introduces are in scope.

## 3. Skeleton terms and types

A skeleton term is built only from:

1. variables, each free, naming an entry in the scope (§7), or bound,
   referring to a binder of a telescope that has not been opened;
2. applications of a type constructor, `Type` among them (§2);
3. applications of a value constructor.

A binder gets an entry in two ways. It is opened, getting a fresh
entry, when its telescope is checked, when a body, branch or pattern
`let` is entered, and at the results of a call, a match or `sorry`. It
is instantiated, getting an existing entry, when an entry is checked
against it or bound to it: a call's or application's argument, a result
checked against returns or an annotation, or a `let`'s right-hand side.

Each application in a skeleton term must check against the telescope of
the type constructor or value constructor it applies (§8). A type is a skeleton term of type `Type()`. Type checking
is: canonicalize both sides by the `is` facts in force (§7), then
compare for identity.

`Type() : Type()`. There is no universe hierarchy and no positivity
requirement. Uniqueness of identity proofs (Axiom K) is derivable.

## 4. First-class values

Types are first class: a value of type `Type()` is allowed to be passed,
returned, bound and stored in a field of a value constructor. A value of
type `Type()` cannot be the scrutinee of a `match` or pattern `let`.

Functions, type constructors and value constructors are not first
class. They are applied, never passed, returned, bound or stored.

## 5. Data types

```
data T(params) : Type() {
  C(fields) : T(args);
  ...
}
```

Each value constructor declares its own telescope of fields, and returns
`T` applied to one argument per parameter of `T`. The arguments are
skeleton terms (§3) and are allowed to refer to the value constructor's
fields and to any entry in scope, a top-level one included. The
parameters of `T` are in scope only in its own telescope: a value
constructor that needs one declares its own field for it. A type
constructor declared by `data` is a data type constructor, and an
application of one is a data type. A `data` declaration is written only
at the top level, alone or in a `mutual` block, and is allowed to
declare no value constructors.

Mutually recursive `data` declarations are written together in a
`mutual` block; a `data` declaration outside any `mutual` block is a
group of its own, and no `mutual` block holds both `data` declarations
and functions. Within a group, a type constructor's telescope is allowed
to mention the group's earlier type constructors, and a value
constructor's fields and return are allowed to mention every type
constructor of the group and the group's earlier value constructors.

```
mutual {
  data Even(n : Nat()) : Type() {
    EvenZero() : Even(Zero());
    EvenSucc(n : Nat(), p : Odd(n)) : Even(Succ(n));
  }
  data Odd(n : Nat()) : Type() {
    OddSucc(n : Nat(), p : Even(n)) : Odd(Succ(n));
  }
}
```

## 6. `is`

`x is e` is allowed in place of `x : T` in function parameters and
returns, value-constructor fields, match annotations, `let` binders and
`sorry`'s telescope, but not in type-constructor parameters. The type of
`x` is then the type of `e`, and `e` must be a skeleton term (§3). When
a binder `x is e` is opened (§3), its fresh entry gets the rule that it
is `e`; when it is instantiated, the entry it gets must canonicalize to
the same skeleton term as `e`. Either way, each bound variable in `e`
stands for the entry its binder got.

A `let` binder is allowed to carry a type, an `is` clause, or neither. A
type or `is` clause written on a `let` binder must be canonically
identical to what the checker infers, so `let y is Succ(n) = e;` asserts
a fact the checker must already know.

## 7. What the checker knows

The checker keeps a scope of entries. Each entry has a type and can have
an `is` rule, a rewrite from the entry to a skeleton term (§3).
Canonicalizing a skeleton term rewrites it by these rules to a fixed
point.

The checker knows only what it can infer from the text. After
`let x = VCons(Nat(), Zero(), Zero(), VNil(Nat()));`, `x` canonicalizes
to `VCons(Nat(), Zero(), Zero(), VNil(Nat()))`. The results of a
function call or of `sorry` are new entries known only by their types,
except where the function's return telescope or `sorry`'s telescope
states an `is` (§6).

Every application of a type constructor or value constructor, and every
result of a call, is an entry of its own, usually anonymous. An
application's entry `x` has the rule `x is F(a1, ..., an)`, where `F` is
the type constructor or value constructor applied and each `ai` is its
argument's entry.

**Forcing.** Entering a match branch equates the scrutinee with the
branch's value constructor applied to fresh fields, and the scrutinee's type
with that application's type. Both sides of an equation are
canonicalized first. Two applications of the same type constructor, or
of the same value constructor, are equated argument by argument, and an equation between a term and itself
is dropped. An entry `x` is given the rule `x is e`; when `e` is an
entry too, the newer of the two takes the rule. Whenever an entry is
equated with a term, their types are equated too. The facts last until
the branch ends, or, for a pattern `let`, to the end of the enclosing
block, or, at the top level, of the program (§10). Forcing fails, refuting the branch, when:

1. an entry is equated with a skeleton term that strictly contains it;
2. two applications of different type constructors, of different value
   constructors, or one of each, are equated.

## 8. Functions

```
fn name(params) -> (returns) { body }
```

Functions are defined only at the top level. There are no nested
functions and no closures. Mutually recursive functions are written
together in a `mutual` block, their **group**; a function outside any
`mutual` block is a group of its own.

A function returns one or more values. The return telescope can depend
on the parameters and on earlier returns; its names are in scope in its
later entries, not in the body.

A block, `{ s1; ...; sn; e }`, is an expression: zero or more statements
followed by a final expression, whose results are the block's. A
statement in a block is a tuple or pattern `let`, or `inspect;`, and
`let x = e;` is `let (x) = e;`, a tuple `let` with one binder.
A function's body is a block, and a block is allowed wherever an
expression is, such as a match branch. A program is a sequence of
declarations (`data`, `fn` and `mutual`) and top-level statements:
`let` in every form, `comptime` pattern `let` included, `inspect;`,
`print e;`, `goal T;` and `qed e;`.

A tuple `(a1, ..., an)` has at least one element, so `()` is not an
expression, and `(a)` is a tuple of one. Each element produces one
value, and the tuple produces `n`. A call produces one value per return,
a match one per annotation entry, `sorry(telescope)` one per entry of
its telescope, and a block what its final expression produces; any
other expression produces one.

A function body must produce one value per return, a branch body one per
annotation entry, a tuple `let`'s right-hand side one per
binder, and a block's final expression what the block must produce.
Anywhere else, a pattern `let`'s right-hand side included, an expression
must produce one value. A function has at least one return, a match
annotation and `sorry`'s telescope at least one entry, and a tuple
`let` at least one binder; a pattern `let`'s value constructor can
have no fields.

```
fn vuncons(A : Type(), n : Nat(), v : Vec(A, Succ(n)))
    -> (hd : A, tl : Vec(A, n)) {
  let VCons(_, _, h, t) = v;
  (h, t)
}
```

`let (h, t) = vuncons(A, n, v);` binds its two results.

The arguments of a call are checked in order. Each argument is an entry
(§7), and each parameter is instantiated to its argument's entry (§3).
So in `f(a1, ..., an)`, each `ai` is checked against its parameter's
type, which can mention `a1` to `a(i-1)`'s entries through the earlier
parameters, and the call's results are the fresh entries `f`'s returns
are opened to, which mention the arguments' entries through the
parameters. An application of a type constructor or a value constructor
is checked the same way. A type-constructor application has type
`Type()`. A value-constructor application has its value constructor's
return as its type, with each field instantiated to its argument's
entry. For example, `VCons(Nat(), Zero(), x, VNil(Nat()))` needs
`x : Nat()` and `VNil(Nat()) : Vec(Nat(), Zero())`, and its type
canonicalizes to `Vec(Nat(), Succ(Zero()))`.

A body's or a branch's results are checked against its return telescope
or annotation in the same way: each return or annotation entry is
instantiated to the entry of the result produced for it. A parameter is
opened when the body is entered, so the body refers to its entry
directly.

## 9. Termination

A body is allowed to call:

- any function of an earlier group, with no annotation;
- a function of its own group, under the decrease below.

Parameters are allowed to be marked `subterm`, including `is` parameters
(`subterm m is Succ(n)`). A call within the group marks, for some `k`,
the argument for the callee's `k`-th `subterm` parameter `subterm e`,
and the argument for each of its earlier `subterm` parameters `same e`;
every other argument is unmarked. The call is accepted when the caller
has at least `k` `subterm` parameters and:

- the `subterm` argument is a strict subterm of the caller's own `k`-th
  `subterm` parameter;
- each `same` argument for the callee's `i`-th `subterm` parameter is
  canonically identical to the caller's own `i`-th `subterm`
  parameter.

In a scope, a term `s` is a strict subterm of a term `t` when,
canonicalized by the facts in force, `t` is an application
`F(t1, ..., tn)` of a type constructor or a value constructor, and `s`
is canonically identical to one of `t1` to `tn` or is a strict subterm
of one. The marks are always written; none is inferred.

```
fn ack(subterm m : Nat(), subterm n : Nat()) -> (r : Nat()) {
  match m : (r : Nat()) {
    Zero() => Succ(n);
    Succ(m1) => match n : (r : Nat()) {
      Zero() => ack(subterm m1, Succ(Zero()));
      Succ(n1) => ack(subterm m1, ack(same m, subterm n1));
    };
  }
}
```

In `ack(subterm m1, Succ(Zero()))` the second argument is unmarked,
since only the callee's `subterm` parameters up to the one marked
`subterm` are marked. In the `Succ(m1)` branch, `m` canonicalizes to
`Succ(m1)`, so `m1` is a strict subterm of it.

Code at the top level calls any function, with no annotation.

## 10. Matching

```
match e : (telescope) {
  C(x1, ..., xn) => body;
  ...
}
```

In a `match`, and in a pattern `let` (below), the type of `e` must
canonicalize to a data type (§5).

The annotation is mandatory; it is the telescope the match produces, so
a match may return several values. Its names are in scope in its later
entries, as a return telescope's are (§8). It is checked in the scope
before the match. Each branch's results are checked against it in the branch's
scope, where forcing has refined it. The match's results are new entries
typed by the annotation as it stands before the match. `_` in its place
reuses the telescope the position expects.

A branch binds one name per field of its value constructor; its body is
an expression, often a block (§8). Patterns do not nest: each field is
bound to a name, or to `_`. Every value constructor has at most one
branch. A value constructor is **refuted** when its forcing fails (§7);
a refuted value constructor has no branch, and every other value
constructor has one. So a match whose scrutinee's data type constructor
declares no value constructors has no branches. A branch for a refuted
value constructor is an error.

A value constructor is refuted only at a `match` or pattern `let`, and only by
what is known about the scrutinee and its type (§7). Suppose a value in
scope is a proof that rules out `C` for the scrutinee. That value does
not automatically refute `C`, so the match must still have a branch for
`C`. In that branch, the program can match on the proof. If every value
constructor of the proof's type is refuted there, that match has no
branches:

```
data IsZero(n : Nat()) : Type() {
  IsZeroHere() : IsZero(Zero());
}

fn f(n : Nat(), p : IsZero(n)) -> (r : Nat()) {
  match n : (r : Nat()) {
    Zero() => Zero();
    Succ(m) => match p : (r : Nat()) {};
  }
}
```

Here the scrutinee is `n`, and `p` is a proof that rules out `Succ` for
`n`. `p` does not automatically refute `Succ`, so the match on `n` has a
branch for `Succ`. In that branch, `p : IsZero(Succ(m))`, while
`IsZeroHere()` has type `IsZero(Zero())`, so `IsZeroHere` is refuted
and the match on `p` has no branches.

A pattern `let`, `let C(x1, ..., xn) = e;`, is a statement. Exactly one
value constructor of `e`'s type must survive forcing, and it must be `C`; its
fields and facts stay in scope for the rest of the enclosing block. A
pattern `let` is not allowed at the top level in phase 1, where
`comptime let` (§11) takes its place. A later phase might allow it once
programs can be built as executables (§16).

## 11. Compile time

A program has no run-time stage: code is evaluated only at compile
time, and only when asked to, by `print` (§12) and two top-level
statements:

- `comptime let x = e;` evaluates `e` during checking. The checker
  knows of `x` exactly what it would know after `let x = e;`.
- `comptime let C(x1, ..., xn) = e;` evaluates `e` during
  checking and requires the result to be headed by `C`; otherwise it is
  an error showing the value. It is then checked as a pattern `let`
  (§10), except that the run, not forcing, rules out the other
  value constructors, and its fields and facts stay in scope for the rest of
  the program.

This is how a proof by reflection is written, given

```
data Option(A : Type()) : Type() {
  None(A : Type()) : Option(A);
  Some(A : Type(), x : A) : Option(A);
}
```

and a function `decideEven(n : Nat()) -> (r : Option(Even(n)))`, with
`Even` as in §5:

```
comptime let Some(_, p) = decideEven(Succ(Succ(Zero())));
```

After it, `p : Even(Succ(Succ(Zero())))`.

In both forms of `comptime let`, `e` is allowed to refer only to
functions, type constructors, value constructors and earlier `comptime`
bindings.

## 12. `sorry`, `print`, `goal` and `qed`

`sorry` is an expression of any type, and checking goes on past it as
past any other expression. The interface reports whether a program
contains `sorry` anywhere. Once an evaluation reaches `sorry`, the
program evaluates nothing more: from there on, every `print` shows
`sorry` and every `comptime` pattern `let` is accepted without its head
check.

`print e;` is a top-level statement that evaluates `e` at compile time
and shows its value, as a tree of applications of type constructors and
value constructors, beside the statement. As in a `comptime let` (§11), `e` is allowed to
refer only to functions, type constructors, value constructors and
`comptime` bindings.

`goal T;` sets the program's goal, a type. `qed e;` checks `e` against
it. Each is a top-level statement and appears at most once in a program,
`qed` after `goal`. The goal is proved when the `qed` checks and the
program contains no `sorry`. A `qed` that checks in a program containing
`sorry` proves nothing; the interface reports that the `qed` checks
and that the program contains `sorry`.

A tutorial page shows one or more read-only boxes of source above the
learner's editable box, and checks them all as one program, in order,
under a phase the page chooses (§16).
Whether the learner's box must hold the `qed` is up to the page.

## 13. Seeing what the checker sees

At any position in a program, the interface shows:

- **Expected**: the telescope still to be produced there.
- **Termination**: the enclosing function's `subterm` parameters, in order,
  and the functions of its group.
- **Scope**: the local entries, each with its type and `is` rule, and,
  in phase 2, whether it is erased.
- **Refutations**, at a `match` or pattern `let`: the refuted value
  constructors. Clicking one shows why its forcing fails (§7), as a
  derivation with the fewest steps.

Hidden until the learner opens them, the **Globals** are the top-level
names in scope at that position: each function, with its parameters and
returns; each type constructor, with its parameters and its value
constructors, each with its fields and return; and each top-level
binding, with its type and `is` rule, marked `comptime` or not.

Types and skeleton terms are shown canonicalized. An anonymous entry is
shown by a marker giving what kind of entry it is and where it was
created. Clicking a skeleton
term, in the source, in the interface or in text typed into it, shows
its canonical form and a sequence of rewrites with the fewest steps that
produces it. Each `is` rule a derivation or a sequence of rewrites uses
links to where its fact was created.

In the interface's interactive mode, a type or an expression typed in is
checked in the scope at the selected position, and its type and `is`
rule are shown, both as inferred and canonicalized.

Functions appear under Termination and among the Globals, never under
Scope, because they are not first class (§4); they are still in the one
namespace (§2).

The statement `inspect;` reports the same information as text.

## 14. Implementation

Checking produces, for the code it evaluates, a separate syntax tree
with erased positions removed, and a tree-walking interpreter evaluates
that tree.

## 15. Not in phase 1

Every binder has multiplicity `many`; no multiplicity is written. There
are no literals, strings, characters or input. `_` is inferred only in
place of a match annotation. A pattern `let` without `comptime` is not
allowed at the top level (§10).

Pledge has no uniqueness, no `at` and no coercions, in any phase.

## 16. Later phases

Phase 2 adds erasure. Every binder has a multiplicity, `many` or
`erased`: function parameters and returns, value-constructor fields, the
binders of every kind of `let`, and match annotation entries.
A binder is `many` unless written `erased`.
Type-constructor arguments are always erased. Value constructors
themselves are never erased, and every value built by one carries its
tag.

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

## 17. Review status

The owner has skimmed the introduction and §1 to §6 and tentatively
approved their wording. The other sections have not yet been reviewed.

## 18. Keywords

`comptime`, `data`, `fn`, `goal`, `inspect`, `is`, `let`, `match`,
`mutual`, `print`, `qed`, `same`, `sorry`, `subterm`. Phase 2 adds
`erased` and `many` (§16).
