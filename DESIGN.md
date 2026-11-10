# Pledge

Pledge is a language for teaching restricted dependent types. It runs in
a web browser and is implemented in TypeScript. Its main interface shows
what the type checker knows at any point of a program (§13).

The language comes in phases, each a superset of the one before. A
program is checked under one phase, chosen by the learner or by a
tutorial page (§12), with the features of that phase and of every
earlier one. This file describes phase 1; §16 describes phase 2 and
what is planned beyond it.

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
§19 gives the grammar.

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

There is one namespace, and no name is allowed to be shadowed: a declaration or binder
is not allowed to reuse a name that is in scope where it is written, other than its own, or
a keyword. A telescope, a pattern or a tuple `let` is not allowed to
introduce one name twice. A name
refers to a value, a function, a type constructor or a value
constructor. `Type` is a built-in type constructor with no parameters,
and not a data type constructor (§5); `Type()` is the type of every
type, itself included (§3, §4). Only a value is allowed to be passed,
returned, bound or stored.

Names come into scope in the order they are written. A function's own
name is in scope in its telescopes and body, and every function a `mutual` block
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
checked against returns or an annotation, or a tuple `let`'s right-hand side.

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
returns, value-constructor fields, match annotations, tuple `let` binders and
`sorry`'s telescope, but not in type-constructor parameters. The type of
`x` is then the type of `e`, and `e` must be a skeleton term (§3). When
a binder `x is e` is opened (§3), its fresh entry gets the rule that it
is `e`; when it is instantiated, the entry it gets must canonicalize to
the same skeleton term as `e`. Either way, each bound variable in `e`
stands for the entry its binder got.

A tuple `let` binder is allowed to carry a type, an `is` clause, or neither.
The binders of a tuple `let` are a telescope (§1): a type or `is` clause
is allowed to refer to the binders before it, but not to one that
carries neither. A
type or `is` clause written on a tuple `let` binder must be canonically
identical to what the checker infers for the result it names (§8), so `let y is Succ(n) = e;` asserts
a fact the checker must already know.

## 7. What the checker knows

The checker keeps a scope of entries. Each entry has a type and can have
an `is` rule, a rewrite from the entry to a skeleton term (§3).
Canonicalizing a skeleton term rewrites it by these rules to a fixed
point.

The checker knows only what it can infer from the text, and, after a
`comptime` pattern `let`, which value constructor a run produced (§11). After
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

**Forcing** a value constructor at a match or pattern `let` equates the scrutinee with
that value constructor applied to fresh fields, and the scrutinee's type
with that application's type. Both sides of an equation are
canonicalized first. Two applications of the same type constructor, or
of the same value constructor, are equated argument by argument, and an equation between a term and itself
is dropped. An entry `x` is given the rule `x is e`; when `e` is an
entry too, the newer of the two takes the rule. Whenever an entry is
equated with a term, their types are equated too. In a match, the facts of forcing a
branch's value constructor last until
the branch ends; for a pattern `let`, they last to the end of the enclosing
match branch or function body, or of the program (§10). Forcing fails, refuting the value constructor (§10), when:

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
`mutual` block is a group of its own. A `mutual` block is allowed to
hold functions that do not call each other.

A function returns one or more values. The return telescope can depend
on the parameters and on earlier returns; its names are in scope in its
later entries, not in the body.

A block, `{ s1; ...; sn; e }`, is an expression: zero or more statements
followed by a final expression, whose results are the block's. A
statement in a block is a tuple or pattern `let`, or `inspect;`, and
`let x = e;` is `let (x) = e;`, a tuple `let` with one binder. A tuple
`let` binder names the entry produced for it and adds no entry and no
rule: after `let y = x;`, `x` and `y` are two names for one entry. A
tuple `let`'s binders are in scope after the `let`, to the end of the
enclosing block, or, at the top level, of the program.
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

Some positions give the expression there what it must produce. A
function body is given its returns, a branch body the match's
annotation (§10), and a `qed`'s expression the goal (§12). A tuple
`let` gives its right-hand side its binders, a binder with neither a
type nor an `is` clause taking any result. A block gives its final
expression what the block is given. A call or application gives each
argument its parameter or field, and a tuple gives each element the
matching entry of what the tuple is given, the earlier entries being
instantiated to the entries of the earlier arguments or elements.
Nothing else is given. An expression's results are checked against what
it is given as a call's arguments are against its parameters: each
entry is instantiated to the entry of the result produced for it. So a
block's results are checked against what the block is given in the
block's scope, with the block's facts in force (§7). A parameter is
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
every other argument is unmarked. Only a call within the group has
marks. The call is accepted when the caller
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
a match can produce several values. Its names are in scope in its later
entries, as a return telescope's are (§8). It is checked in the scope
before the match. Each branch's results are checked against it in the branch's
scope, where forcing has refined it. The match's results are new entries
typed by the annotation as it stands before the match.

`_` in place of the annotation, or of `sorry`'s telescope (§12), stands
for the telescope given at its position (§8). It is allowed only where
a whole telescope is given: at a function body, a branch body, the
right-hand side of a tuple `let` whose binders all carry a type or an
`is` clause with no `_` in it (§20), and a block's final expression at
one of these. At a
`qed`'s expression, whether it is allowed is an implementation choice
(§14). This `_` never stands for one entry of a telescope, so it is not
allowed at a tuple's element; a `_` at an argument is the form of §20.

Each branch is for a value constructor of the scrutinee's data type
constructor. Patterns do not nest: a branch gives the fresh entry each
field of its value constructor is opened to (§3) a name, or `_`. Its
body is an expression, often a block (§8).
Every value constructor has at most one
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

A pattern `let`, `let C(x1, ..., xn) = e;`, is a statement, in a block
or at the top level. Exactly one value constructor of `e`'s type must
survive forcing, and it must be `C`; its names are in scope for the rest
of the enclosing block; its fields and facts last to the end of the
enclosing match branch or function body, or of the program. A `comptime` pattern `let` (§11) differs only in what rules out
the other value constructors.

## 11. Compile time

A program has no run-time stage: code is evaluated only at compile
time. Each top-level statement is evaluated as soon as it is checked,
every `let` included, except for what taint removes (§12). Only `print`
shows a value, apart from the error of a `comptime` pattern `let`
below. A value is a tree of applications of value constructors, with a
blank in place of each type and, in phase 2, of each erased value
(§16). No type is evaluated: an application of a type constructor is
skipped, with everything in it, and gives a blank.

Evaluation is eager: a call evaluates its arguments, in order, before
its body, and a block evaluates its statements in order, then its final
expression. A match evaluates its scrutinee, then the branch for the
value constructor that heads the value, with the branch's fields bound
to the value's arguments; a pattern `let` binds its fields the same
way.

`comptime let C(x1, ..., xn) = e;` is a top-level statement. It
evaluates `e` during checking and requires its value to be headed by
`C`; otherwise it is an error showing the value. It is then checked as
a pattern `let` (§10), except that the run, not forcing, rules out the
other value constructors: `C` must survive forcing, and the others need
not be refuted. Its fields and facts stay in scope for the rest of the
program. `comptime` is written only on a pattern `let`, and only at the
top level.

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

After it, `p : Even(Succ(Succ(Zero())))`. Without `comptime`, the
`let` would be an error, since forcing does not refute `None`.

## 12. `sorry`, `print`, `goal` and `qed`

`sorry(telescope)` is an expression that produces one new entry per
entry of its telescope, described by it, types and `is` rules alike
(§6), so `sorry(x is Zero())` produces one entry, whose rule is that it
is `Zero()`. Its telescope's names are in scope only in its later
entries, as a match annotation's are (§10). `sorry(_)` stands for the
telescope given at its position (§10). Checking goes on past `sorry` as
past any other expression.

Any use of `sorry` is unsound; **taint** tracks what relies on one. It
is decided from the text, without evaluation, and comes from how a
result is produced, never from canonicalization:

- every result of `sorry` is tainted;
- an application's result is tainted when any argument's is; a tuple's
  or a block's result when the matching result of its element or final
  expression is; and a match's result when the scrutinee's result or
  the matching result of any branch is;
- every result of a call is tainted when the function is tainted or any
  argument's result is;
- a function is tainted when any result of its body is; within a group,
  every function starts untainted, and taint spreads until nothing more
  becomes tainted;
- a tuple `let` binder is tainted when the result it binds is, and so
  is the result of every use of it;
- a scope is tainted when a fact forced from a tainted scrutinee is
  in force in it (§7): each branch of a `match` whose scrutinee is
  tainted, and, after a pattern `let`, plain or `comptime`, whose
  scrutinee is tainted, the rest of the match branch or function body
  it is in, or, at the top level, of the program; every result
  produced in a tainted scope is tainted;
- a `_` (§20) is tainted when the term it is solved to mentions a
  tainted entry;
- nothing else is tainted.

So a function whose body binds a tainted result that reaches none of
its results is untainted, and a call to it is tainted only by its
arguments, though the program still contains `sorry`.

Before code is evaluated, every expression whose results are all
tainted is removed, with everything in it, so evaluation never reaches
a `sorry`. An unread `let` whose right-hand side is a match on a
`sorry`, for example, is never evaluated, and a match only some of
whose results are tainted still runs, for the others. A `comptime`
pattern `let` whose scrutinee is tainted evaluates nothing, so it does
not check that the value is headed by its value constructor. After a
top-level pattern `let`, plain or `comptime`, whose scrutinee is
tainted, nothing evaluates, every `print` shows `sorry` and no `qed`
proves the goal, though checking goes on.

`print e;` is a top-level statement that evaluates `e` and shows its
value beside the statement, as a tree of applications of value
constructors, with `_` in place of each type and, in phase 2, of each
erased value (§11, §16). When `e`'s result is tainted, it
evaluates nothing and shows `sorry`.

`goal T;` sets the program's goal, a type, checked in the scope where
it is written, and `goal fn (params) -> (returns);` sets a goal that is
a function signature, its telescopes checked as a function's are (§8),
with no name and no body. `qed e;` checks `e` against a type goal;
`qed f;`, naming a function, checks `f`'s parameter and return
telescopes against a function goal's, which must be canonically
identical position by position, binder names aside, compared as terms
whose bound variables refer to their binders, so an earlier binder's
`is` clause is not in force for later ones; `is` clauses and, in
phase 2, multiplicities must agree, and `subterm` marks are not
compared. Each is a top-level
statement and appears at most once in a program, `qed` after `goal`.
The goal is proved when the `qed` checks, the results of `T` and of `e`,
or the goal's telescopes and `f`, are untainted, and no top-level
pattern `let` whose scrutinee is tainted comes before the `qed`.
`qed f;` passes, returns and stores nothing (§4); it names a
declaration. The interface reports
whether the program contains `sorry` anywhere, whether the `qed` checks,
or was not reached, and whether the goal is proved.

A tutorial page shows one or more read-only boxes of source above the
learner's editable box, and checks them all as one program, in order,
under a phase the page chooses (§16). Line numbers run on from one
box to the next.
Whether the learner's box must hold the `qed` is up to the page.

## 13. Seeing what the checker sees

At any position in a program, the interface shows:

- **Expected**: what the position is given (§8) and is still to be
  produced there, with an explicit indication wherever nothing has been
  determined: where nothing is given, and for a tuple `let` binder with
  neither a type nor an `is` clause.
- **Termination**: the enclosing function's `subterm` parameters, in order,
  and the functions of its group.
- **Scope**: every entry in the scope at that position (§7) that is
  not global, in the order the entries were created, each with its
  names, which of them are tainted (§12), its type and its `is` rule,
  and, in phase 2, whether it is erased; and whether the scope is
  tainted, with the scrutinee that tainted it. An entry with several
  names (§8) is shown once, with all of them. An entry with no name is
  listed under its marker, like any other entry. An entry is global
  when a top-level statement created it, named or not; the global
  entries are among the Globals. At the top level, where every entry in
  scope is global, Scope lists none and points to the Globals instead.
- **Refutations**, at a `match` or pattern `let`: the refuted value
  constructors, and, at an erased match (§16), the absurd branches.
  Clicking one shows, in a dialog, why its forcing fails (§7), as a
  derivation with the fewest steps: `suppose`, then the match or
  pattern `let`, with `erased` or `comptime` as written, as
  `match s { P => ... }` or `let P = s;`, where `s` is the scrutinee's
  entry and `P` the value constructor applied to the fresh entries its
  fields are opened to (§3), then the equations that lead to the
  failure, and the equation that gave each rule one of them is
  rewritten by. Each field's fresh entry is named as in the branch or
  pattern written for the value constructor, if any; otherwise it is
  shown as `@` and the field's declared name.

The **Globals** come in two parts, each hidden until the learner opens
it. One lists the global entries in scope at that position, each shown
as under Scope. The other lists the functions and type constructors in
scope there: each function, with its parameters and returns; and each
type constructor, with its parameters and its value constructors, each
with its fields and return.

Types and skeleton terms are shown canonicalized, except where this
section says otherwise. An anonymous entry is
shown by a marker giving where it was
created: `_@line:column` at the `_` that made or bound it, and
otherwise `?@line:column`, with a number after the `?` when several
were created at one position. Clicking a skeleton
term, in the source, in the interface or in text typed into it, shows
its canonical form and a sequence of rewrites with the fewest steps that
produces it. Clicking or hovering over a `_` that stands for a
telescope (§10) or is in place of an argument or inside a type (§20)
shows what it stands for: the telescope, or the term the `_` is solved to. Each `is` rule a
derivation or a sequence of rewrites uses links to where its fact was
created.

Under Expected and Scope, and among the global entries, a type or `is`
rule has a dialog only when the dialog gives information that its row,
and its entry's name if it has an entry, do not: when its raw form
differs from its canonical form, or when it is an entry's `is` rule
made, or an entry's type defined, somewhere other than where the entry
was created. A raw form is the term as the checker has it, before
canonicalizing (§7). An entry's type is defined by the binder the entry
was opened from (§3); for the entry of an application, by the declared
return of the value constructor applied, or by the declaration of the
data type constructor (§5) applied; and otherwise, as for an
application of `Type`, where the entry was created. The dialog shows:

- the raw form, and, for an entry's `is` rule made, or an entry's type
  defined, somewhere other than where the entry was created, where it
  was made or defined;
- the `is` rules that canonicalizing it applies, numbered, each written
  `x → e`;
- the rewriting from the raw form to the canonical form, one rule per
  step, each step citing its rule's number.

Each rule in the dialog's list can be opened to show how the rule was
made:

- a rule from forcing: the derivation that gave it, starting with the
  match or pattern `let` as under Refutations, without `suppose`;
- a rule from solving a `_` (§20): the derivation that gave it;
- any other rule: that it is the rule of an application (§7) or of an
  `is` clause (§6).

Outside the dialog's list, wherever a rule is stated as a fact, it is
written `x is e`. A derivation, in the dialog or under Refutations,
shows the entry of an unnamed application by its marker, not as the
application.

TBD:

- how the derivations are shown when several rules in the list come
  from one forcing (for now, each in full);
- whether a rule cited inside a derivation can itself be opened (for
  now, it cannot);
- the wording that says a rule is that of an application or of an `is`
  clause.

In phase 2, the interface sets erased code in italics: every expression
in an erased position (§16) other than a type, with everything inside
it; each erased binder's name where it is bound, with its `erased`; at
an erased match, `erased`, the scrutinee, the patterns and the absurd
branches; and a `let` whose binders are all erased, or an erased
pattern `let`, as a whole.

In the interface's interactive mode, a type or an expression typed in is
checked in the scope at the selected position, and its type and `is`
rule are shown, both as inferred and canonicalized.

Functions appear under Termination and among the Globals, never under
Scope, because they are not first class (§4); they are still in the one
namespace (§2).

The statement `inspect;` reports the same information as text, beside
the statement.

Checking stops at the first error, which the interface shows where it
occurs. A program that does not parse is checked up to the declaration
or statement that fails to parse.

## 14. Implementation

Checking produces, for the code it evaluates, a separate syntax tree
without what taint removes (§12) and, from phase 2 on, without erased
positions (§16); a tree-walking interpreter evaluates that tree.

Whether `_` is allowed at a `qed`'s expression, standing for the goal,
so whether `qed sorry(_);` is allowed, is an implementation choice.

## 15. Not in phase 1

Every binder has multiplicity `many`; no multiplicity is written. There
are no literals, strings, characters or input.

Pledge has no uniqueness, no `at` and no coercions, in any phase.

## 16. Later phases

Phase 2 adds erasure. Every binder has a multiplicity, `many` or
`erased`: function parameters and returns, value-constructor fields, the
binders of every kind of `let`, and match annotation entries.
A binder is `many` unless written `erased`. A multiplicity is written
immediately before the binder's name, after `subterm`; an explicit
`many` is allowed wherever `erased` is.
Type-constructor arguments are always erased. Value constructors
themselves are never erased, and every value built by one carries its
tag.

An erased name is allowed only in an erased position: a type, an
argument for an erased parameter or field, the result for an erased
return or binder, and everything inside these. A call whose results are
all erased takes any arguments. Evaluation skips erased positions.

`match erased e : (...)` and `let erased C(...) = e;` take their
scrutinee erased; a match without a multiplicity is `many`. A destructure binds a field erased when the
field or the match is erased, and `many` otherwise. An erased match with
a `many` annotation entry has at most one branch that is not absurd; a
branch is absurd when its body is a match with no branches, possibly
the final expression of a block, and evaluation runs the branch that is
not absurd.

`_` in place of an annotation takes the given telescope with its
multiplicities.

Phase 3 is to be designed later. It will allow creating an executable,
a program with input and output.

## 17. Review status

The owner has confirmed the wording of the introduction and §1 to §9,
apart from edits not yet reviewed; the rest of the file awaits review.

## 18. Keywords

`comptime`, `data`, `fn`, `goal`, `inspect`, `is`, `let`, `match`,
`mutual`, `print`, `qed`, `same`, `sorry`, `subterm`. Phase 2 adds
`erased` and `many` (§16).

## 19. Grammar

The grammar of phase 1, without the extra `;` that §1 allows. `NAME` is
a name that is not a keyword (§1, §18); `[x]` is an optional `x`, `x*`
is zero or more `x`, and `x+` is one or more.

```
program   ::= (data | fn | mutual | statement | topstatement)*
mutual    ::= 'mutual' '{' (data+ | fn+) '}'
data      ::= 'data' NAME '(' [typed (',' typed)*] ')' ':' 'Type' '(' ')'
              '{' (NAME '(' [binders] ')' ':' term ';')* '}'
typed     ::= id ':' term
fn        ::= 'fn' NAME '(' [param (',' param)*] ')' '->' '(' binders ')' block
param     ::= ['subterm'] binder
binders   ::= binder (',' binder)*
binder    ::= id (':' term | 'is' term)
id        ::= NAME | '_'
term      ::= NAME | NAME '(' [term (',' term)*] ')' | '_'
block     ::= '{' statement* expr '}'
statement ::= 'let' letlhs '=' expr ';' | 'inspect' ';'
topstatement ::= 'comptime' 'let' pattern '=' expr ';'
              | 'print' expr ';' | 'qed' expr ';'
              | 'goal' (term | 'fn' '(' [param (',' param)*] ')' '->' '(' binders ')') ';'
letlhs    ::= '(' letbinder (',' letbinder)* ')' | letbinder | pattern
letbinder ::= id [':' term | 'is' term]
pattern   ::= NAME '(' [id (',' id)*] ')'
expr      ::= NAME | NAME '(' [arg (',' arg)*] ')' | '(' expr (',' expr)* ')'
              | block | match | sorry
arg       ::= ['subterm' | 'same'] (expr | '_')
match     ::= 'match' expr ':' ('(' binders ')' | '_') '{' (pattern '=>' expr ';')* '}'
sorry     ::= 'sorry' '(' (binders | '_') ')'
```

A `NAME` followed by `(` in `expr` is a call when it names a function,
and otherwise an application of the type constructor or value
constructor it names. Only a call within its group has marks (§9).

## 20. `_` for an argument or inside a type

`_` is allowed in place of an argument of a call, or of an application
of a type constructor or value constructor (§8), when the argument is:

1. erased where it stands (§16); or
2. for a parameter or field whose type is `Type()`.

It is also allowed in place of a whole type, or of a term anywhere
inside one.

`_` is also allowed in place of a match annotation or `sorry`'s
telescope, where it stands for the telescope given at its position
(§10).

Each `_` in place of an argument or inside a type stands for a skeleton
term (§3), found by unification alone. Where a result is checked
against what its position is given (§8), a `_` on either side is solved
to whatever makes the two identical.

A `_` must be solved by the end of the innermost of these that it is
written in: a call; a function body; a branch body; a scrutinee; a
pattern `let`'s right-hand side; a tuple `let`; a `print`'s or `qed`'s
expression; a type or `is` term written in a telescope. An application
of a type constructor or value constructor does not end it.

The term must have the type of the `_`'s position and satisfy its
parameter's `is` clause. It must also mention only entries that exist
before the `_`.

A tuple `let`'s binders are checked before its right-hand side, with
their `_` unsolved, and the right-hand side is given them. A `_` in a
binder is allowed to mention what the right-hand side produces.

A `_` that is not solved so is an error.
