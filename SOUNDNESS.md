# Why Pledge appears sound

A Claude session wrote this note at the owner's request. Any claim in it
that the owner has not made may be mistaken. Section numbers are those
of DESIGN.md.

**How rigorous it is.** The note defines a semantics and a typing of
values, states its lemmas precisely, and proves each by a written
induction. It is not machine-checked, and part 9 lists what it takes on
trust: chiefly that the checker implements §3 to §12 as the declarative
rules of part 4 describe them. It follows the shape of Sleight's
SOUNDNESS.md, which argues the same points for a larger language.

## In short

Pledge has `Type : Type` and no positivity requirement (§3). The usual
paradoxes seem not to reach it:

1. **Types never compute.** A type contains no call (§3), and the
   checker evaluates only where `comptime` or `print` asks it to (§11,
   §12).
2. **Termination does not come from types.** Every call goes down in an
   order made of the definition order of groups and the `subterm`
   parameters (§9), and neither looks at a type.
3. **Functions are not first class** (§4). No type mentions a function,
   so no datatype holds one. Curry's paradox, and Girard's in Hurkens'
   form, seem to need function types over `Type`, which cannot be
   written.
4. **Value typing recurses on the value.** Whether a value has a type is
   decided by recursion on the value's tree (part 2), so `Type : Type`
   creates no circularity in what a type means.

## 1. What is claimed

For every phase 1 program the checker accepts that contains no `sorry`:

- **(C)** Checking terminates (part 7).
- **(T)** Every evaluation terminates (part 6).
- **(P)** Every evaluation produces values of the types, and satisfying
  the `is` rules, that the checker assigned (part 5).
- **(K)** If the program has `goal T;` and `qed e;`, then `T` has a
  value. In particular, no `qed` proves a type with no constructors,
  such as `False` (part 8).

A program that contains `sorry` anywhere is outside the claims. Since
nothing runs at compile time that the program's text does not ask for
(§11), the presence of `sorry` is a property of the text alone, which is
why reporting it for the whole program suffices (§12).

## 2. Values and their types

Fix the program's declarations. A **value** is a finite tree:

    v ::= Type | T(v1, ..., vn) | C(v1, ..., vn)

with `T` a type constructor and `C` a value constructor, applied to as
many values as they have parameters or fields. Values of type `Type`
are exactly the trees built from `Type` and type-constructor
applications; values of other types are value-constructor applications.

For a telescope `Delta = (x1 j1, ..., xn jn)`, each `ji` being `: A` or
`is e`, write `(v1, ..., vn) |= Delta` when for every i, with
`s = [x1 := v1, ..., x(i-1) := v(i-1)]`:

- if `ji` is `: A`, then `|- vi : A s`;
- if `ji` is `is e`, then `vi = e s`, and `|- vi : B s` for the type
  `B` the checker gave `e`.

Here `A s` is the substitution of values for variables in a term,
which, types containing no calls, is again a value. The judgment
`|- v : V` is defined by recursion on `v`:

- `|- Type : V` iff `V = Type`;
- `|- T(v1..vn) : V` iff `V = Type` and `(v1..vn) |= Delta_T`;
- `|- C(v1..vn) : V` iff `(v1..vn) |= Delta_C` and
  `V = T(u1..um) [fields := v1..vn]`, where `T(u1..um)` is `C`'s
  declared return.

Each clause refers to `|-` only at the strict subtrees `vi`, so the
definition is well-founded by the size of `v`, whatever `V` is. This is
where `Type : Type` costs nothing: the judgment never recurses on a
type.

**Lemma 2.1 (inversion).** If `|- v : T(u1..um)` then `v = C(w1..wn)`
for a value constructor `C` declared under `T`. *Proof:* the first two
clauses give type `Type`, not an application of `T`; the third gives
`C`'s declared return, which is an application of the type under which
`C` is declared (§5). ∎

**Lemma 2.2 (unique types).** If `|- v : V` and `|- v : V'` then
`V = V'`. *Proof:* each clause determines `V` from `v`. ∎

**Corollary 2.3.** No value has type `T(...)` for a `T` with no
constructors.

**Lemma 2.4 (subtrees).** For terms `t'` and `t` and any substitution
`s` of values for their variables, if `t'` is a strict subterm of `t`
through applications (§9), then `t' s` is a strict subtree of `t s`.
*Proof:* substitution maps `F(t1..tn)` to `F(t1 s, ..., tn s)`, so each
argument position of `t` is an argument position of `t s`. ∎

There is no infinite descending chain of strict subtrees, since values
are finite.

## 3. Contexts, facts and valuations

The checker's scope `Gamma` (§7) is a sequence of entries, each with a
type `A_x`, a term, and possibly a rule `x -> e_x`. A **valuation**
`rho` maps entries to values. `rho |= Gamma` when, for every entry `x`:

- `|- rho(x) : A_x rho`, and
- if `x` has a rule, `rho(x) = e_x rho`.

Write `t rho` for the value of term `t`. The rules of `Gamma` are
**acyclic**: no entry reaches itself by following rules. Write
`canon(t)` for `t` rewritten by the rules to a fixed point, which
exists by acyclicity.

**Lemma 3.1 (canonicalization is sound).** If `rho |= Gamma` then
`canon(t) rho = t rho`. *Proof:* each rewrite replaces an entry `x` by
`e_x`, and `rho(x) = e_x rho`; substitution is compositional. ∎

**Corollary 3.2.** If `rho |= Gamma`, two terms with the same canonical
form have equal values, and a term that is a strict subterm of another
after canonicalization has a value that is a strict subtree of the
other's (with Lemma 2.4).

**Lemma 3.3 (forcing).** Let `rho |= Gamma`, let `s` be a term with
type `S` in `Gamma`, and let `s rho = C(w1..wn)`. Forcing `s` against
`C(f1..fn)`, the `fi` fresh entries with `C`'s field types, succeeds,
and the context `Gamma'` it produces satisfies
`rho' = rho[f1 := w1, ..., fn := wn] |= Gamma'`, with `Gamma'`'s rules
acyclic.

*Proof.* First, `rho' |= Gamma, f1..fn`: by Lemma 2.1 and the third
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
- **An entry `x` with no rule against a term `e`**: if `x` occurs in `e`
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
  term. The results are fresh entries typed by `f`'s return telescope,
  with rules for its `is` returns.
- **Bodies.** A function's body checks against its return telescope: its
  results' types and `is` rules canonicalize to the instantiated
  returns.
- **`let` and constructor application** forward what the right-hand
  side's checking produced; a written type or `is` clause is
  canonically identical to it.
- **`match`** lists a branch for every constructor of the scrutinee's
  type that forcing does not refute, checks each branch in the context
  forcing produced, and checks each branch's results against the
  annotation.
- **`let-match`** is a `match` with one branch whose body is the rest of
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

- **Constructor application.** The arguments' values satisfy the
  constructor's telescope by the induction hypothesis and Corollary 3.2,
  so the application has the instantiated return type by the third
  clause of part 2.
- **Call.** The same argument gives `args |= Delta_params`, the
  precondition of the induction hypothesis for the body, whose results
  then satisfy the return telescope, `is` returns included.
- **`let`.** Immediate from the right-hand side, with Corollary 3.2 for a
  written type or `is` clause.
- **`match`.** The scrutinee's value has the scrutinee's type, an
  application of some `T` (a value of type `Type` is never matched, §4),
  so by Lemma 2.1 it is `C(w...)` for a constructor `C` of `T`. By Lemma
  3.3, `C` is not refuted, so the match has a branch for `C`, and the
  valuation extended by the fields satisfies the branch's context. The
  induction hypothesis on the branch body gives results satisfying the
  annotation in that context, and the annotation mentions only entries
  outside the branch.
- **`let-match`.** As `match`, with the rest of the body as the branch.
- **`comptime let-match`.** The evaluator's result is headed by the
  written `C`; the rest is as `let-match`. This rests on the evaluator
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
call within the group at slot `k` (§9) keeps the first component, passes
to each callee slot before `k` a `same` argument canonically identical
to the caller's parameter there, hence equal by Corollary 3.2, and
passes to callee slot `k` a canonical strict subterm of the caller's
`k`-th parameter, hence a strict subtree. Later slots may hold anything,
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
induction. A `match` has a branch for its scrutinee's constructor by the
`match` case of Theorem 5.1. The top level is not a function and runs
straight through its statements. ∎

Theorems 5.1 and 6.2 are proved together: 6.2's call case uses 5.1 on
the arguments, and 5.1's induction is on the derivation 6.2 provides.

## 7. Checking terminates (C)

Canonicalization ends because the rules are acyclic (part 3). Forcing
ends (Lemma 3.3), and so does comparison for identity. `_` in place of
an annotation copies a telescope the position already has. Compile-time
evaluation, by `comptime` and `print`, ends by Theorem 6.2. Nothing
here looks at whether `Type` contains itself.

## 8. Consistency (K)

Suppose a program checks with `goal T;` and `qed e;`. The top-level
statements before the `qed` evaluate (Theorem 6.2) to a valuation
`rho` satisfying the top-level context (Theorem 5.1); this is the full
semantics, in which ordinary top-level `let`s are evaluated too,
although Pledge never evaluates them (§11). Then `e` evaluates to a
value `v` with `|- v : T rho`. If `T` is an application of a type
constructor with no constructors, Corollary 2.3 rules this out. ∎

## 9. What is taken on trust

- **The checker implements part 4.** The note proves the declarative
  rules sound, not the TypeScript code. In particular it assumes that
  entries are distinct however they are named, that
  forcing and canonicalization follow part 3, and that rules leave the
  scope with the entries they mention (§7).
- **The evaluator** computes the semantics of part 5. The facts a
  `comptime let-match` adds depend on it.
- **Phase 2.** Erasure is argued only in outline: evaluation that skips
  an erased computation uses its declared results, which by Theorems 5.1
  and 6.2 would have been produced and would have satisfied them. An
  erased match with a `many` result has at most one branch (§16), so it
  needs no tag it lacks. The typing of part 2 would need erased fields
  to be checked like any other, since they still constrain types.

## 10. What the argument leans on

If any of these changed, the argument would need revisiting:

- a call, or any evaluation, inside a type or in canonicalization;
- first-class functions, or a function type in a type, which would add a
  value whose typing does not recurse on a smaller tree;
- the subterm check accepting a term that is not a strict subterm, or
  looking through anything but constructor and type-constructor
  applications;
- recursion by any route other than a call under §9's rule;
- a way to build a telescope by evaluation, which would remove the
  bound k;
- matching on a value of type `Type`.
