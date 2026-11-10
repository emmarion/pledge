# Why Pledge appears sound

A Claude session wrote this note at the owner's request. Any claim in it
that the owner has not made may be mistaken. Section numbers are those
of DESIGN.md.

**How rigorous it is.** The note defines a semantics and a typing of
values, states its lemmas precisely, and proves each by a written
induction. The note itself is not machine-checked, and part 9 lists
what it takes on trust: chiefly that the checker implements §3 to §12
as the declarative rules of parts 4 and 12 describe them. It follows
the shape of Sleight's
[SOUNDNESS.md](https://github.com/emmarion/sleight/blob/main/SOUNDNESS.md),
which argues the same points for a larger language. A second
implementation of the checker and evaluator, in Lean under `lean/`,
comes with Lean-checked counterparts of most of the lemmas below, for
programs without `_` arguments (§16) under phase 1 or 2, `sorry`
included, so their statements take in taint (§12), which part 12
argues, and erasure (§16), which part 9 argues only in outline.
Parts 11 and 12 list them. Those results are about the Lean
implementation and about the definitions as formalized there, not
about the TypeScript code.

## In short

Pledge has `Type() : Type()` and no positivity requirement (§3). The usual
paradoxes seem not to reach it:

1. **Types never compute.** A type contains no call (§3), and the
   checker evaluates only top-level statements, as they are checked
   (§11, §12), never inside a type.
2. **Termination does not come from types.** Every call goes down in an
   order made of the definition order of groups and the `subterm`
   parameters (§9), and neither looks at a type.
3. **Functions are not first class** (§4). No type mentions a function,
   so no datatype holds one. Curry's paradox, and Girard's in Hurkens'
   form, seem to need function types over `Type()`, which cannot be
   written.
4. **Value typing recurses on the value.** Whether a value has a type is
   decided by recursion on the value's tree (part 2), so `Type() : Type()`
   creates no circularity in what a type means.

In a program that contains `sorry`, the claims are about what taint
(§12) leaves untainted, and taint keeps `sorry` away from them (part
12).

## 1. What is claimed

For every phase 1 program the checker accepts:

- **(C)** Checking terminates (part 7).
- **(T)** Every evaluation terminates (part 6).
- **(P)** Every evaluation produces values of the types, and satisfying
  the `is` rules, that the checker assigned (part 5).
- **(K)** If the program has `goal T;` and a `qed` that proves the goal
  (§12), then `T` has a value. In particular, no `qed` proves a type
  whose data type constructor declares no value constructors, such as
  `False()` (part 8).

Parts 2 to 8 argue these for a program that contains no `sorry`. In a
program that contains `sorry`, evaluation is of what taint leaves
(§12), (P) is claimed for untainted results only, and in (K) `T` has a
value under a valuation of the top-level entries that satisfies the
top-level scope as it is at the `qed`; part 12 argues these. Since
nothing runs at compile time that the program's text does not ask for
(§11), the presence of `sorry` is a property of the text alone, which is
why reporting it for the whole program suffices (§12).

## 2. Values and their types

Fix the program's declarations. A **value** is a finite tree:

    v ::= T(v1, ..., vn) | C(v1, ..., vn)

with `T` a type constructor and `C` a value constructor, applied to as
many values as they have parameters or fields; `Type()` is the
application of the type constructor `Type` to no values. Values of type
`Type()` are exactly the trees built from type-constructor applications;
values of other types are value-constructor applications.

For a telescope `Delta = (x1 j1, ..., xn jn)`, each `ji` being `: A` or
`is e`, write `(v1, ..., vn) |= Delta` when for every i, with
`s = [x1 := v1, ..., x(i-1) := v(i-1)]`:

- if `ji` is `: A`, then `|- vi : A s`;
- if `ji` is `is e`, then `vi = e s`, and `|- vi : B s` for the type
  `B` the checker gave `e`.

Here `A s` is the substitution of values for variables in a skeleton term,
which, types containing no calls, is again a value. The judgment
`|- v : V` is defined by recursion on `v`:

- `|- T(v1..vn) : V` iff `V = Type()` and `(v1..vn) |= Delta_T`;
- `|- C(v1..vn) : V` iff `(v1..vn) |= Delta_C` and
  `V = T(u1..um) [fields := v1..vn]`, where `T(u1..um)` is `C`'s
  declared return.

Each clause refers to `|-` only at the strict subtrees `vi`, so the
definition is well-founded by the size of `v`, whatever `V` is. This is
where `Type() : Type()` costs nothing: the judgment never recurses on a
type.

**Lemma 2.1 (inversion).** If `|- v : T(u1..um)` for a data type
constructor `T` then `v = C(w1..wn)` for a value constructor `C`
declared under `T`. *Proof:* the first clause gives type `Type()`, and
`Type` is not a data type constructor (§2); the second gives `C`'s
declared return, which is an application of the data type constructor
under which `C` is declared (§5). ∎

**Lemma 2.2 (unique types).** If `|- v : V` and `|- v : V'` then
`V = V'`. *Proof:* each clause determines `V` from `v`. ∎

**Corollary 2.3.** No value has type `T(...)` for a data type
constructor `T` that declares no value constructors.

**Lemma 2.4 (subtrees).** For skeleton terms `t'` and `t` and any substitution
`s` of values for their variables, if `t'` is a strict subterm of `t`
in a scope with no facts (§9), then `t' s` is a strict subtree of `t s`.
*Proof:* substitution maps `F(t1..tn)` to `F(t1 s, ..., tn s)`, so each
argument position of `t` is an argument position of `t s`. ∎

There is no infinite descending chain of strict subtrees, since values
are finite.

## 3. Contexts, facts and valuations

The checker's scope `Gamma` (§7) is a sequence of entries, each with a
type `A_x`, a skeleton term, and possibly a rule `x -> e_x`. A **valuation**
`rho` maps entries to values. `rho |= Gamma` when, for every entry `x`:

- `|- rho(x) : A_x rho`, and
- if `x` has a rule, `rho(x) = e_x rho`.

Write `t rho` for the value of skeleton term `t`. The rules of `Gamma` are
**acyclic**: no entry reaches itself by following rules. Write
`canon(t)` for `t` rewritten by the rules to a fixed point, which
exists by acyclicity.

**Lemma 3.1 (canonicalization is sound).** If `rho |= Gamma` then
`canon(t) rho = t rho`. *Proof:* each rewrite replaces an entry `x` by
`e_x`, and `rho(x) = e_x rho`; substitution is compositional. ∎

**Corollary 3.2.** If `rho |= Gamma`, two skeleton terms with the same canonical
form have equal values, and a skeleton term that is a strict subterm of another
in `Gamma` (§9) has a value that is a strict subtree of the
other's (with Lemma 2.4).

**Lemma 3.3 (forcing).** Let `rho |= Gamma`, let `s` be a skeleton term with
type `S` in `Gamma`, and let `s rho = C(w1..wn)`. Forcing `s` against
`C(f1..fn)`, the `fi` fresh entries with `C`'s field types, succeeds,
and the context `Gamma'` it produces satisfies
`rho' = rho[f1 := w1, ..., fn := wn] |= Gamma'`, with `Gamma'`'s rules
acyclic.

*Proof.* First, `rho' |= Gamma, f1..fn`: by Lemma 2.1 and the second
clause of part 2, `(w1..wn) |= Delta_C`, which is what the fields' types
ask. Forcing processes a set of equations `t = t'`. Its invariant is
that every pending equation holds under `rho'`, that is, `t rho' =
t' rho'`, and that `rho' |= Gamma''` for the context `Gamma''` built so
far. Initially the equations are `s = C(f1..fn)`, which holds by
assumption, and `S = C(f1..fn)`'s type, which holds by Lemma 2.2, since
`|- s rho : S rho` and `|- C(w1..wn) : (its type) rho'`. Each step
canonicalizes both sides (Lemma 3.1 keeps the equation true) and then:

- **Same head**, `F(t1..tk) = F(t'1..t'k)`: replaced by `ti = t'i`. These
  hold because equal trees with the same head have equal children.
- **Different heads**: the two sides are trees with different roots,
  which cannot be equal. So this case does not arise, and forcing does
  not fail here.
- **An entry `x` with no rule against a skeleton term `e`**: if `x` occurs in `e`
  at a strict position, `rho'(x)` would be a strict subtree of itself
  by Lemma 2.4, so this does not arise either. If `e` is `x`, the
  equation is dropped. Otherwise the rule `x -> e` is added; it holds,
  and since `x` does not occur in `canon(e)` the rules stay acyclic. The
  equation between `x`'s type and `e`'s type is then added; it holds by
  Lemma 2.2, since both are the type of one value. When `e` is itself an
  entry, the newer of the two takes the rule (§7), which is the same
  argument.

Each step either shrinks the equations or removes an entry with no rule
from among those that can still take one, so forcing ends. Every
failure case of §7 has been shown not to arise. ∎

Contrapositively, if forcing refutes `C`, no valuation satisfying the
context makes `s` headed by `C`.

## 4. The rules, as this note reads them

The note takes the checker to implement the following, which are its
reading of §6 to §12.

- **Expressions.** `Gamma |- e => Delta` says that `e` checks in
  `Gamma`, producing results described by the telescope `Delta` (types
  and `is` rules), and leaves the context `Gamma` extended by its
  statements' entries.
- **Calls.** At a call `f(a1..an)`, the arguments' canonical types match
  `f`'s parameter telescope instantiated by the earlier arguments, and an
  argument for an `is` parameter canonicalizes to the instantiated `is`
  skeleton term. The results are fresh entries typed by `f`'s return telescope,
  with rules for its `is` returns.
- **Bodies.** A function's body checks against its return telescope: its
  results' types and `is` rules canonicalize to the instantiated
  returns.
- **`let` and the application of a type constructor or value
  constructor** forward what the right-hand
  side's checking produced; a written type or `is` clause is
  canonically identical to it.
- **`match`** lists a branch for every value constructor of the scrutinee's
  type that forcing does not refute, checks each branch in the context
  forcing produced, and checks each branch's results against the
  annotation.
- **A pattern `let`** is a `match` with one branch whose body is the rest of
  the enclosing body.
- **Termination** follows §9.

## 5. Preservation (P)

Evaluation is eager and big-step: `rho |- e => vs`, the values `vs` of
`e`'s results, with function calls evaluating the body in a valuation of
the parameters. The top level evaluates in order.

**Theorem 5.1.** If `Gamma |- e => Delta`, `rho |= Gamma` and
`rho |- e => vs`, then `vs |= Delta rho`, and the valuation extended by
the entries `e`'s statements add satisfies the extended context.

*Proof,* by induction on the derivation of `rho |- e => vs`, by cases:

- **Application of a type constructor or value constructor.** The
  arguments' values satisfy the telescope by the induction hypothesis
  and Corollary 3.2, so the application has the instantiated return type
  by the first or the second clause of part 2.
- **Call.** The same argument gives `args |= Delta_params`, the
  precondition of the induction hypothesis for the body, whose results
  then satisfy the return telescope, `is` returns included.
- **`let`.** Immediate from the right-hand side, with Corollary 3.2 for a
  written type or `is` clause.
- **`match`.** The scrutinee's value has the scrutinee's type, a data
  type (§10), an application of some data type constructor `T`, so by
  Lemma 2.1 it is `C(w...)` for a value constructor `C` of `T`. By Lemma
  3.3, `C` is not refuted, so the match has a branch for `C`, and the
  valuation extended by the fields satisfies the branch's context. The
  induction hypothesis on the branch body gives results satisfying the
  annotation in that context, and the annotation mentions only entries
  outside the branch.
- **Pattern `let`.** As `match`, with the rest of the body as the branch.
- **`comptime` pattern `let`.** The evaluator's result is headed by the
  written `C`; the rest is as a pattern `let`. This rests on the evaluator
  computing what this semantics computes (part 9).

∎

## 6. Totality (T)

Number the groups 0, 1, 2, ... in definition order, and let k be the
largest number of `subterm` parameters of any function in the program,
finite because telescopes are program text. Give an activation of a
function in group g, whose `subterm` parameters hold values
s1, ..., sn, the measure

    mu = (g, s1, ..., sn, TOP, ..., TOP)

padded to length k + 1 with TOP, a value above every tree. Order
measures lexicographically, the first component by number and the others
by strict subtree, with TOP above everything. Each component is
well-founded and there are k + 1 of them, so the order is.

**Lemma 6.1.** Under a valuation satisfying the caller's context, the
callee's measure is below the caller's at every call in a body.
*Proof.* A call to an earlier group has a smaller first component. A
call within the group that marks the callee's `k`-th `subterm`
parameter `subterm` (§9) keeps the first component, passes to each of
the callee's earlier `subterm` parameters a `same` argument canonically
identical to the caller's parameter at that position, hence equal by
Corollary 3.2, and passes to the callee's `k`-th a canonical strict
subterm of the caller's `k`-th, hence a strict subtree. Later
`subterm` parameters may hold anything,
which lexicographic order allows. §9 makes the marked arguments those
for the callee's own `subterm` parameters, which is what lets these
values be the callee's measure. ∎

**Theorem 6.2.** For every `e` with `Gamma |- e => Delta` and every
`rho |= Gamma`, `rho |- e => vs` for some `vs`. *Proof,* by
well-founded induction on the measure of the enclosing activation, and
inside it by induction on the syntax of `e`. Every construct other than
a call evaluates its parts, finitely many and syntactically smaller.
A call's arguments satisfy the callee's context by Theorem 5.1, and its
measure is smaller by Lemma 6.1, so its body evaluates by the outer
induction. A `match` has a branch for its scrutinee's value constructor by the
`match` case of Theorem 5.1. The top level is not a function and runs
straight through its statements. ∎

Theorems 5.1 and 6.2 are proved together: 6.2's call case uses 5.1 on
the arguments, and 5.1's induction is on the derivation 6.2 provides.

## 7. Checking terminates (C)

Canonicalization ends because the rules are acyclic (part 3). Forcing
ends (Lemma 3.3), and so does comparison for identity. `_` in place of
an annotation copies a telescope the position already has. Compile-time
evaluation of each top-level statement ends by Theorem 6.2. Nothing
here looks at whether `Type()` contains itself.

## 8. Consistency (K)

Suppose a program checks with `goal T;` and `qed e;`. The top-level
statements before the `qed` evaluate (Theorem 6.2) to a valuation
`rho` satisfying the top-level context (Theorem 5.1), every top-level
`let` included, as §11 has it. Then `e` evaluates to a
value `v` with `|- v : T rho`. If `T` is a data type whose data type
constructor declares no value constructors, Corollary 2.3 rules this
out. ∎

In a program that contains `sorry`, the statements before the `qed`
need not evaluate to such a valuation; Theorem 12.4 takes their place.

## 9. What is taken on trust

- **The checker implements parts 4 and 12.** The note proves the
  declarative rules sound, not the TypeScript code. In particular it
  assumes that entries are distinct however they are named, that
  forcing and canonicalization follow part 3, that a match branch's
  rules leave the scope with the branch, that a pattern `let`'s
  rules, which Lemma 3.3 makes consequences of the typing, last to the
  end of the enclosing match branch or function body, or of the program
  (§7, §10), and that taint is computed, and code removed, as part 12
  reads §12. For the Lean implementation, the theorems of parts 11 and
  12 are about its code instead.
- **The evaluator** computes the semantics of part 5, on what taint
  leaves (part 12). The facts a `comptime` pattern `let` adds depend on
  it.
- **Phase 2.** Erasure is argued only in outline: evaluation that skips
  an erased computation uses its declared results, which by Theorems 5.1
  and 6.2 would have been produced and would have satisfied them. An
  erased match with a `many` result has at most one branch that is not
  absurd (§16), an absurd branch being one whose body refutes every
  value constructor of some scrutinee, so by Lemma 3.3 it is never
  taken, and the match needs no tag it lacks. The typing of part 2 would need erased fields
  to be checked like any other, since they still constrain types.
  Part 11 lists the Lean theorems about erasure in the Lean
  implementation; this note's argument for it stays an outline.

## 10. What the argument leans on

If any of these changed, the argument would need revisiting:

- a call, or any evaluation, inside a type or in canonicalization;
- first-class functions, or a function type in a type, which would add a
  value whose typing does not recurse on a smaller tree;
- the subterm check accepting a skeleton term that is not a strict subterm, or
  looking through anything but constructor and type-constructor
  applications;
- recursion by any route other than a call under §9's rule;
- a way to build a telescope by evaluation, which would remove the
  bound k;
- matching on a value of type `Type()`;
- an untainted result computed from the value of a tainted one other
  than through a type or an `is` rule, or code that taint removes
  being evaluated (part 12).

## 11. The Lean counterparts

`lean/README.md` describes the Lean implementation, the model its
theorems are stated in and what they assume. Lean checks the theorems
below for programs without `_` arguments (`Program.holeFree`), under
any phase, with or without `sorry`, with no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`. Each is meant to be the
counterpart of the part of this note it is listed under; the
correspondence is a Claude session's reading and may be inexact. File
names are under `lean/Pledge/`.

The Lean statements split this note's single evaluation in two: an
ideal valuation, which plays the role of `rho` here, and run-time
values, which the evaluation relation computes and from which taint
and erasure remove parts. A run-time value is related to an ideal one
by `Rel`, or by `Approx` at an erased position (`Core.lean`).

- **Part 2.** `HasType` and `TeleSat` (`Core.lean`) define the typing of
  values. They type values by closed signatures, the program's
  signatures with the values of the top-level entries they mention
  substituted (`Sig.close`), so that typing depends on no valuation.
- **Lemma 2.1:** `HasType.inv_type`; **Lemma 2.2:** `HasType.unique`;
  **Corollary 2.3:** `HasType.empty` (all in `CoreLemmas.lean`), with
  `ownedBy_empty` (`Sound/Data.lean`) for a data type constructor that
  declares no value constructors; **Lemma 2.4:** `Term.strictSub_eval`
  (`UnifySound.lean`).
- **Part 3.** `Sat` (`Core.lean`) is `rho |= Gamma`, except that a
  tainted entry's value need only have its type by its head (`WType`):
  it is part 12's `rho |=~ Gamma`.
  **Lemma 3.1:** `Term.eval_canon` (`CoreLemmas.lean`); **Corollary
  3.2:** `Sat.eval_eq_of_identical` (`CoreLemmas.lean`) and
  `isStrictSubterm_sound` (`UnifySound.lean`); **Lemma 3.3:**
  `solve_sound`, `force_good` and `force_refuted` (`UnifySound.lean`).
- **Part 4** has no counterpart: the Lean theorems are about the Lean
  checker's code, not about declarative rules.
- **Theorems 5.1 and 6.2,** proved together as in part 6: `Expr.sound`
  and `Stmt.sound` (`Sound/Expr.lean`) for an expression or statement
  under an invariant on an untainted scope, the valuation and the
  functions available, and `FnGroup.GroupOk.fnSpec` (`Sound/Fn.lean`)
  for the untainted functions of a group, by well-founded induction on
  the measure of part 6 (`Act`, `Sound/Measure.lean`). Here
  `rho |- e => vs` is the relation `Eval` (`Eval.lean`), big-step and
  with no measure; the measure appears only in the proof, and these
  theorems say that a derivation exists, to run-time values related to
  ideal values that satisfy what the checker assigned.
- **Lemma 6.1:** `call_lt` (`Sound/Basic.lean`), with `Act.lt_wf`
  (`Sound/Measure.lean`) for the well-foundedness of the order.
- **(P) and (T)** for the top level: `runProgram_sound`,
  `reached_eval_ok` and `reached_run_ok` (`Sound/Top.lean`), the last
  two saying that each top-level evaluation has a derivation of `Eval`,
  not that the executable evaluator, a `partial` function, finds it.
- **(K):** `type_goal_inhabited`, `fn_goal_holds` and `no_empty_goal`
  (`Sound/Top.lean`), and `run_sound` and `run_no_empty_goal` for source
  text whose parsed program is hole-free; with `sorry`, the valuation
  they give satisfies the top-level scope at the `qed` (`ProvedAt`,
  Theorem 12.4). `lean/README.md` lists ways in which these statements
  are weaker than they may first read.
- **(C)** has no theorem. Every definition of the Lean implementation
  other than the executable evaluator is total, by structural or
  well-founded recursion, with no fuel. The evaluator is `partial`: each
  result it returns carries a derivation of `Eval`, but nothing
  establishes that it returns, so the Lean implementation does not
  show that compile-time evaluation ends.
- **Taint (§12)** enters the statements above: an untainted entry or
  result is typed and a tainted one need not be; the invariant and the
  main lemma assert nothing once a scope is tainted; and a tainted
  function has no specification. Part 12 names the Lean counterpart of
  each of its steps beside it.
- **Part 9's outline for phase 2:** `matchErased_sound` and
  `patletErased_sound` (`Sound/Expr.lean`) for an erased `match` and
  pattern `let`, with `ExprSound` (`Sound/Defs.lean`) stating that an
  absurd expression in a scope that stays untainted has only tainted
  results; the run-time values of erased positions are related to
  ideal ones by `Approx` alone.

The following have no Lean counterpart: programs with `_` arguments,
and so §16's unification and taint through a `_`, which this note does
not argue either; the TypeScript implementation; and the parsers, about
which no theorem says anything. That the Lean checker implements
DESIGN.md is not proved either; it is supported only by comparing its
verdicts with the TypeScript checker's on a corpus of programs
(`lean/tests/README.md`).

## 12. Programs that contain `sorry`

This part extends parts 3 to 8 to a phase 1 program that contains
`sorry`. Beside each step it names the Lean theorem or definition that
checks its counterpart in the Lean implementation, for programs
without `_` arguments in phases 1 and 2 (part 11); file names are
under `lean/Pledge/`, and the correspondence is a Claude session's
reading.

**The idea.** `sorry(x : False())` has no value, so a program with
`sorry` can have no valuation satisfying part 3. The argument gives
each entry an ideal value all the same, which for a tainted entry may
be junk: a tree `junk(A)` that records the type `A` the entry is meant
to have, and that no clause of part 2 types. Every value still has its
type by its head, so forcing and the `is` rules work as before; only
untainted results are claimed to have their types. A tainted scope,
one in force after a pattern `let` or in a branch on a tainted
scrutinee, carries no claim at all, and everything checked in it is
removed. What remains to check is that taint misses nothing: that no
untainted result is computed from the value of a tainted one, and that
nothing taint leaves needs a value it removed.

### Junk and satisfaction

Add to the values of part 2 a tree `junk(A)` for every value `A`.
Write `|-h v : V`, `v` has type `V` by its head, when `v = junk(V)`, or
`v = F(v1..vn)` and `V` is `F`'s declared return with its parameters or
fields replaced by `v1..vn` (`Type()` for a type constructor). It looks
at `v`'s head and arguments, not at their types. If `|- v : V` then
`|-h v : V`, and `|-h` determines `V` from `v` as in Lemma 2.2. No
clause of `|-` applies to `junk`, so Lemma 2.1 and Corollary 2.3 hold
as before. (`WType`, `Value.junk`, `HasType.wtype`, `WType.unique` and
`HasType.empty`, in `Core.lean` and `CoreLemmas.lean`.)

`rho |=~ Gamma` when, for every entry `x`:

- `|-h rho(x) : A_x rho`;
- if `x` has a rule, `rho(x) = e_x rho`;
- if `x` is untainted, `|- rho(x) : A_x rho`.

(`Sat`, with `WSat` for the first two, in `Core.lean`.) Without
`sorry`, every entry is untainted and `|=~` is part 3's `|=`.

**Lemma 12.1.** Lemma 3.1 and Corollary 3.2 hold for `|=~`, and so
does Lemma 3.3 when the scrutinee is untainted, its fields being
untainted. *Proof:* Lemma 3.1 and Corollary 3.2 use only the rules.
In Lemma 3.3, the scrutinee's value is typed, so Lemma 2.1 gives its
head and the fields' values are typed; each equation between types is
between types by head, which `|-h` determines as Lemma 2.2 does. ∎
(`Term.eval_canon`, `Sat.eval_eq_of_identical`, `force_good`,
`force_refuted`.)

**Lemma 12.2 (opening).** Whatever values the outer entries have, a
telescope the checker accepted can be opened to values that meet it by
their heads: an entry `x : A` takes `junk(A s)`, and an entry `x is e`
takes `e s`, which has by its head the type of `e` (§6), `s` being the
values of the outer and earlier entries. `A s` and `e s` are values
whatever `s` is, since a type and an `is` clause are skeleton terms,
with no call (§3). ∎ (`WantsCons`, `telescope_cons`,
`annotation_cons`, and `FnOk.cons` for a function's returns.)

### The taint rules

The note reads §12 as follows. Beside each rule is the Lean lemma for
its construct, about the Lean checker's implementation of it
(`Sound/Expr.lean`, `Sound/Fn.lean`):

- every result of `sorry` is tainted (`sorry_sound`);
- an application's result is tainted when an argument's is
  (`ctorApp_sound`); a tuple's or a block's result when the matching
  result of its element or final expression is (`tuple_sound`,
  `block_sound`); a match's result when the scrutinee's result or the
  matching result of any branch is (`matchMany_sound`);
- every result of a call is tainted when the function or an argument's
  result is (`call_sound`);
- a group's bodies are checked with the taint of its fixed point (§12),
  and no function untainted there has a tainted result
  (`FnGroup.fixTaint_spec`); a tainted function has no specification
  (`FnOk.defn`, `Sound/Defs.lean`);
- a tuple `let` binder has the taint of the result it binds, and so
  does every use of it (`let_sound`, `var_sound`);
- a pattern `let` on a tainted scrutinee taints the scope after it,
  and every branch of a match on one is checked in a tainted scope
  (`patletMany_sound`, `matchMany_sound`, `comptimeLet_sound`); every
  result produced in a tainted scope is tainted (`checkExpr_removed`,
  `Sound/Shape.lean`).

### What taint removes

An expression whose results are all tainted is removed, with
everything in it; in a tainted scope every result is tainted, so
everything checked there is removed (`checkExpr_removed`). At the top
level, a statement checked in a tainted scope runs nothing, a `print`
of a tainted result shows `sorry`, a `comptime` pattern `let` on a
tainted scrutinee evaluates nothing, and after a top-level pattern
`let` on a tainted scrutinee no `qed` proves the goal. The top level's
invariant is kept through these items by `topStmt_sound`,
`print_sound`, `comptimeLet_sound` and `qed_sound`, with
`TopStmt.tainted` once the scope is tainted (`Sound/Stmt.lean`).

### Preservation and totality with taint

Evaluation is now of the tree taint leaves, from a run-time
environment that gives each name a value; a removed expression
evaluates to a placeholder, `removed`. Say that such an environment
**agrees with** `rho` in a scope when it gives each untainted name its
entry's value under `rho`; a tainted name may have any value, or
`removed` (`EnvRel`, `Sound/Defs.lean`).

**Theorem 12.3.** Let `rho |=~ Gamma` for an untainted scope `Gamma`,
and let `e` check in `Gamma`, given what its position gives it (§8),
with results `r1..rk`. If the scope after `e` is untainted, then:

- (a) there are values `v1..vk`, and values for the entries `e`'s
  statements add, that extend `rho` to a valuation satisfying (`|=~`)
  the scope after `e`; each `vi` has a type by its head, and, when
  `ri` is untainted, `|- vi : B rho` for the type `B` the checker gave
  `ri`; and `v1..vk` meet what `e` is given: each entry's `is` rule,
  and its type, by `|-` for an untainted result and by its head for a
  tainted one;
- (b) from every run-time environment that agrees with `rho`, the tree
  taint leaves of `e` evaluates, and the run-time value of each
  untainted `ri` is `vi`.

If the scope after `e` is tainted, every result of `e` is tainted and
`e` is removed, and nothing is claimed. The same holds of a statement,
with no results. (`ExprPost`, `StmtPost`, `Expr.sound` and
`Stmt.sound`, `Sound/Defs.lean` and `Sound/Expr.lean`. `ExprPost`
states of an untainted result's value that it has some type by `|-`,
not which, besides that the values meet what `e` is given; and it
relates run-time values to ideal ones by `Rel`, which is equality in
phase 1.)

*Proof,* by the induction of Theorems 5.1 and 6.2, now on the measure
of activations of untainted functions only. The cases:

- **`sorry`.** Every result is tainted; Lemma 12.2 gives its values
  from the telescope. It is removed and evaluates to `removed`.
- **A name.** Its entry's value. The environment gives an untainted
  name that value.
- **Application, tuple, block.** As in part 5. A tainted application
  still has the value `F(v1..vn)`, which has its type by its head. A
  block whose statements taint its scope has only tainted results, and
  is removed; its values come from Lemma 12.2 (`block_sound`).
- **Call.** If the function or an argument is tainted, every result is
  tainted, its values come from Lemma 12.2 on the returns, and the
  call is removed. Otherwise the arguments are untainted, so typed, and
  meet the parameters by (a) for each; the callee's measure is below
  the caller's by Lemma 6.1, which uses only Corollary 3.2 and so holds
  by Lemma 12.1 (`call_lt`); and the callee is untainted, so its body's
  results are all untainted, the scope after the body is untainted,
  and the induction hypothesis on the body gives results meeting the
  returns and a run (`FnGroup.GroupOk.fnSpec`, `Sound/Fn.lean`). The
  fixed point is what keeps the induction to untainted functions:
  within the group, a call to a function it leaves tainted has only
  tainted results.
- **Where results are checked (§8).** An expression's results are
  checked against what its position gives it: a body's against its
  returns, a branch body's against the annotation, a `qed`'s against
  the goal, a tuple `let`'s right-hand side against its binders and an
  argument against its parameter. By Corollary 3.2 under Lemma 12.1,
  the values then meet what is given: by `|-` for an untainted result,
  by their heads for a tainted one, and every `is` rule
  (`against_sound`, `Sound/Basic.lean`).
- **Tuple `let`.** Its binders name the right-hand side's results,
  with their values and taints.
- **`match`.** If the scrutinee is tainted, every branch is checked in
  a tainted scope, every result is tainted, the match is removed, and
  Lemma 12.2 on the annotation gives its values. Otherwise the
  scrutinee's value is typed, headed by a value constructor `C` by
  Lemma 2.1, and by Lemma 12.1 `C` is not refuted and the branch for
  `C` has a scope satisfied by `rho` extended by the fields. The
  match's results take the values of that branch's results, which meet
  the annotation as checked there. A result of the match is untainted
  only when the matching result of every branch is, that branch's
  among them, so it has the annotation's type, which mentions only
  entries outside the branch. If that branch's scope ends tainted, all
  its results are tainted, so all the match's are, and Lemma 12.2
  gives their values instead.
  For (b): a match with an untainted result is not removed. Its
  scrutinee is untainted, so its run-time value is its ideal one,
  headed by `C`; the evaluator takes the branch for `C` and binds the
  fields to their values (`EnvRel.pattern`, `Sound/Match.lean`), and
  the branch's untainted results evaluate to their values by the
  induction hypothesis. Its tainted results evaluate to whatever their
  trees give, `removed` for a removed one, which the match passes on
  without inspecting; only the untainted results are claimed
  (`matchMany_sound`, `ResRel`).
- **Pattern `let`.** On an untainted scrutinee, as `match` with the
  rest of the body as the branch; on a tainted one, the scope after it
  is tainted and nothing is claimed (`patletMany_sound`).

In every case, the typing of an untainted result rests only on the
typing of untainted results and on the rules; this is where the
argument needs taint to miss nothing. ∎

**Nothing left needs a removed value.** Part (b) says that the tree
taint leaves has an evaluation by the big-step relation (`Eval`,
`Eval.lean`). That relation has no rule for `sorry`, and none for a
`match` or pattern `let` whose scrutinee's value is `removed`, so the
evaluation of what taint leaves never reaches a `sorry` and never
inspects a removed value. A removed value may still be passed along
unexamined, as the value of a tainted name, a tuple's element or a
match's result. At the top level, `reached_eval_ok` and
`reached_run_ok` (`Sound/Top.lean`) state this for the evaluations a
top-level item performs while the scope is untainted.

### The top level and the goal

While the top-level scope is untainted, there is a valuation `rho`
satisfying (`|=~`) the top-level scope, the top-level run-time
environment agrees with it, and every untainted function meets its
specification; each item keeps this, by Theorem 12.3 for a statement
(`TopInv` and `TopLive`, `Sound/Defs.lean`; `topItems_sound`,
`Sound/Top.lean`). Once the top-level scope is tainted, nothing about
the valuation is kept, and nothing is evaluated (see "What taint
removes").

**Theorem 12.4 (K with `sorry`).** If a `qed` proves the goal `T`, then
`T` has a value under a valuation of the top-level entries that
satisfies (`|=~`) the top-level scope as it is just after the `qed`.
*Proof.* The goal is proved only when the `qed`'s results and `T`'s
are untainted and no top-level pattern `let` on a tainted scrutinee
comes before the `qed` (§12), so the scope at the `qed` is untainted
and the valuation above satisfies it. By Theorem 12.3 (a) and the
check against the goal, the `qed`'s untainted result has a value `v`
with `|- v : T rho`. `T`'s result is untainted too, so
`|- T rho : Type()`, and `T rho` is a type of part 2, not built from
junk. Later items only extend the valuation, the signatures and the
functions, which keeps `|- v : T rho`. ∎

For a function goal, the function the `qed` names is untainted, so it
meets its specification, and its telescopes are canonically identical
to the goal's, so by Corollary 3.2 it meets the goal's (`fnGoal_holds`,
`Sound/Stmt.lean`). Lean checks both cases as `runProgram_sound`, with
`ProvedAt` for the scope at the `qed` and `GoalHolds` for what the goal
states, from `typeQed_sound` and `qed_sound`; its statement does not
include `|- T rho : Type()`.

Since `junk` has no type, Corollary 2.3 still holds, so no `qed` proves
a type whose data type constructor declares no value constructors, in
a program with `sorry` or without (`no_empty_goal`).

### What this part does not cover

- `_` arguments (§16), and so taint through a solved `_` (§12): neither
  this part nor any Lean theorem covers them.
- Erasure: part 9 argues it only in outline; the Lean theorems cover
  phase 2 (`matchErased_sound`, `patletErased_sound`, `Approx`).
- The TypeScript code: this part is about the taint rules as it reads
  them, and the Lean theorems about the Lean implementation, whose
  agreement with the TypeScript checker rests only on the comparison
  of part 11.
- Tainted results: nothing is claimed of their run-time values, which
  need be neither their ideal values nor of their types.
- A function goal holds vacuously when no values satisfy its
  parameters.
