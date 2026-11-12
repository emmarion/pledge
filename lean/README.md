# The Lean implementation

A second implementation of Pledge's checker and evaluator, in Lean 4
with no library beyond Lean's core, together with soundness theorems
that Lean checks for every program, under any phase, `_` (§20),
`sorry` and erasure included. Claude sessions
wrote it, and this file is a Claude session's description of it. As
for the TypeScript implementation, DESIGN.md is the specification, and
where the two disagree, DESIGN.md is right.

## Building and running

With [elan](https://github.com/leanprover/elan), which installs the
toolchain named in `lean-toolchain`:

```sh
cd lean
lake build
.lake/build/bin/pledge check --phase 1 FILE
```

`pledge check --phase N FILE` checks and evaluates the program in
`FILE` under phase `N` and prints one JSON object: `error` (`null` or
`{pos, message}`, `pos` an offset into the source), `prints` (each
`{pos, value}`), `qed` (`none`, `checks`, `fails` or `unreached`),
`goalProved` (`null` when the program has no `goal`), `containsSorry`,
and `inspects` (each `{pos, text}`, the text of an `inspect;`).

```sh
node lean/tests/gate.mjs
```

is the verification gate, run from anywhere with Node 22.18 or later.
It builds; fails on a build error or a `declaration uses 'sorry'`
message; fails if the sources under `Pledge/`, `Pledge.lean` or
`Main.lean`, outside comments and string literals, contain `sorry` as a
term or tactic, `axiom`, `partial`, `unsafe`, `implemented_by`,
`extern`, `opaque`, `native_decide`, `sorryAx`, `admit`,
`skipKernelTC` or anything named like fuel; runs `tests/Audit.lean`,
which prints the axioms of the headline theorems, and fails unless
each uses only `propext`, `Classical.choice` and `Quot.sound`; checks
that `tests/corpus.json` is what `tests/gen-corpus.mjs` writes from
the current `src/`; and runs the differential comparison
(`tests/README.md`), failing on any disagreement. The GitHub Actions
workflow `.github/workflows/lean.yml` runs it on pushes and pull
requests that touch `lean/` or `src/`.

## Layout

- `Pledge/Syntax.lean`, `Lexer.lean`, `Parser.lean`: the syntax of §19
  and §16, and source text to `Program`.
- `Pledge/Core.lean`: terms, values, signatures, entries,
  canonicalization, and the definitions the theorems are stated with:
  `Term.eval`, `HasType`, `TeleSat`, `WType`, `WSat`, `Sat`,
  `Value.junk`, `Approx`, `Rel`, `MultRel`, `Sig.close`.
- `Pledge/Unify.lean`: opening telescopes, `abstract?`, the strict
  subterm relation, `difference` (§12), and the equation solver behind
  forcing (§7) and `_` (§16).
- `Pledge/Eval.lean`: evaluation (§11, §12, §16) as a big-step
  relation, `Eval` with `EvalList`, `CallRel`, `EvalBlock` and
  `EvalStmt`; its determinism (`Eval.det`) and monotonicity in the
  program (`Eval.ext`); and the evaluator, `evalExpr` and its
  companions, which take the fact that what they are given has an
  evaluation and return its values with a derivation of the relation.
  They recurse on what evaluating asks for first (`Cfg.Sub`), which is
  well-founded below anything that has an evaluation (`Eval.acc`).
- `Pledge/Check/Basic.lean`, `Expr.lean`, `Top.lean`: the checker;
  `Top.lean` has the top-level items, `topItem`, and `Outcome`.
- `Pledge/Run.lean`: `topItems`, `checkItems`, `runProgramWith`,
  `solveFrom`, `runProgram` and `run`. It comes after the proofs it
  needs (`Sound/Item.lean`, below): each state `topItems` passes to
  `topItem` carries the fact (`TopOk`) from which what the item
  evaluates has an evaluation (`TopState.Runs`).
- `Main.lean`: the command line.
- `Pledge/CoreLemmas.lean`, `UnifySound.lean`, `Pledge/Sound/`: the
  proofs. `Sound/Defs.lean` worlds, the invariants, the function
  specifications and `GoalHolds`; `Sound/Measure.lean` the measure of
  SOUNDNESS.md part 6 that the totality proof inducts on;
  `Sound/Solution.lean` that a term `coreType` accepts, as the term a
  `_` takes, has a value of its type (`coreType_sound`);
  `Sound/Expr.lean` the main lemma, `Expr.sound` and `Stmt.sound`, by
  one lemma per construct, whose proofs are mostly in
  `Sound/Simple.lean`, `Call.lean`, `Match.lean` and `Erased.lean`;
  `Sound/Fn.lean` and `Data.lean` the declaration groups, and
  `Data.lean` the `goal` item; `Sound/Stmt.lean` the other top-level
  statements; `Sound/Item.lean` that each item keeps the top level's
  invariant (`topItem_sound`) and that, outside the solving pass, what
  the top level evaluates has an evaluation (`TopInv.runs`); and
  `Sound/Top.lean` the headline theorems.
- `Pledge/ParserTest.lean`, `EvalTest.lean`, `UnifyTest.lean`,
  `SolveTest.lean`: `#guard` tests; `EvalTest.lean` runs programs
  through `run`. `SolveTest.lean` holds tests of `_`
  (§20), among them tests of `solution` and of `runProgramWith` given a
  table.

## How `_` is checked

Checking is split in two. `solveFrom` finds, by unification, a table
from the position of each `_` for an argument or inside a type (§20)
to the terms it may stand for, evaluating nothing; `runProgramWith`
then checks and evaluates the program
with no unification for `_` (`Ctx.solving` is false, so no entry is
made for a `_` and every written term, `_` in it or not, is checked by
`checkTerm`): at each `_` it takes the first term of the
table that is a well-formed term of the scope there (`coreType`), of
the `_`'s type, meeting its parameter's `is` clause and §16's rule on
erased names, and it computes the `_`'s taint from that term. A `_`
with no term in the table is an error. `runProgram` runs the two, and
reports an error met by `runProgramWith` that was found by evaluating
(`CheckError.evaluated`, as for a `comptime` pattern `let` whose value
has another head), or else an error met by `solveFrom`; any other error met
only by `runProgramWith` is reported as internal. The soundness theorems are
meant not to depend on `solveFrom`: they hold for `runProgramWith` with
any table.

`solveFrom` checks the program with the table found so far; a `_` the
table does not cover gets an entry of the scope, solved by unification
as the checker did before the split, and at the end of the call,
statement or other boundary it is in (§20), its terms are found and
checking starts again with them. The terms use the numbering of
entries `runProgramWith` has, which has no entry for a `_` or for the
placeholder a tuple `let` binder gets while solving: a number counts
only the entries before it that are neither. The terms offered for a
`_` are, in order, one built from untainted entries that exist before
it wherever canonicalization allows, the term unification first gave
it, and its canonical form when its boundary ends. While solving, a
tuple `let` whose binders have a `_` gives its right-hand side each
binder's type or `is` clause abstracted only over the binders before
it, so a `_` there can be unified with a later binder's placeholder,
which the end of the statement unifies with the result that binder
names. A tuple `let` whose
binders have a `_` is checked by `runProgramWith` right-hand side
first, given only its binders' multiplicities, and then each binder's
type or `is` clause, with the binders before it naming their results,
against the result it names.
- `tests/`: the differential comparison with the TypeScript checker
  (`tests/README.md`), `Audit.lean` and `gate.mjs`.

## The model the theorems use

The theorems relate two kinds of value. An **ideal valuation** gives
each entry of a scope a value, as the valuation of SOUNDNESS.md part 3
does, and values are typed (`HasType`) by the program's signatures
closed by the ideal values of the top-level entries they mention
(`Sig.close`). **Run-time values** are what the evaluation relation
computes, with `removed` where taint or erasure removed code (§12,
§16) and for every application of a type constructor, which the
checker leaves out of the evaluated tree with everything inside it, so
that a value of type `Type()` is `removed` at run time and `print`
shows it as `_`. At a position that is not erased, a run-time value is
related to an ideal one by `Rel`: `removed` for an ideal value headed
by a type constructor, or else the same head, and each argument
related in the same way, except an erased argument, which only
approximates (`Approx`: `removed`, or the same head over approximating
arguments).
At an erased position the relation is `Approx` (`MultRel`).

A tainted entry (§12) need not have a value of its type. `Sat`, the
counterpart of SOUNDNESS.md's `rho |=~ Gamma` (part 12), which is its
`rho |= Gamma` (part 3) when nothing is tainted, asks every entry for a
value without `removed` that agrees with its rule and has its type by
its head (`WType`), and asks only the untainted entries for a value of
their type (`HasType`). The proofs give a result of `sorry` its `is`
clause's value or else `Value.junk A`, an application of `junkHead`,
named `sorry`, to its type `A`, which has `A` by its head and, in the
worlds the proofs use, no type. Once a scope is tainted, nothing is
asserted about its valuation: the main lemma (`ExprPost`, `StmtPost` in
`Sound/Defs.lean`) concludes only when the scope after the expression
or statement is untainted, and the top level's invariant (`TopInv`)
then keeps only the facts that do not depend on the valuation, and a
goal proved before.

A function's specification (`FnSpec` and `CallSpec`) has two halves:
for ideal arguments satisfying the parameters there are ideal results
satisfying the returns, and on run-time arguments related to those
ideal arguments by the parameters' multiplicities, the call
(`CallRel`) returns run-time results related to the ideal results by
the returns' multiplicities. A tainted function has no specification.
`GoalHolds W phase g qedFn` says what a goal `g` means in a world `W`
(`Sound/Defs.lean`): for a type goal, its type evaluates under `W.ρ` to
a value of type `Type()` that some value has as its type; for a function goal, the function `qedFn`
names is in `W`'s functions and meets the goal's telescopes with both
halves of a specification.

## What Lean checks

For any program `prog`, any phase, any `has` (whether the
source is taken to contain a keyword, an argument of `runProgram` with
no default, which `run` reads off the tokens) and any syntax error
`err`, writing `out` for
`runProgram phase prog has err`, Lean checks:

- `runProgram_sound`: there is a world `W` whose evaluator's view of
  the program `W.P` is that of the final top-level state of
  `runProgramWith` with the table `solution phase prog` that
  `solveFrom` finds, whose closed
  signatures `W.Sc` are `out.sigs.map (Sig.close W.ρ)`, whose functions
  are `out.fns`, and whose valuation `W.ρ` has one value per entry of
  `out.entries`; if the final top-level scope is untainted
  (`out.tainted = false`), `W.ρ` satisfies it
  (`Sat W.Sc out.entries W.ρ`); and if `out.goalProved =
  some true`, the goal `out.goal` holds in `W` (`GoalHolds`), and
  `ProvedAt` holds of it: `prog` has a `qed` up to which checking stops
  at no error, the state just after it has the goal proved, an
  untainted scope and the goal `out.goal`, whose entries are all in
  that scope (`GoalBelow`), and the first values of `W.ρ` satisfy that
  scope, typed by its signatures closed by them (`Sat`). The goal is so
  tied to a valuation satisfying the scope as it stood when the goal
  was proved, whatever later items do to the scope.
  `runProgramWith_sound` states the same of `runProgramWith` with any
  table (nothing about `solveFrom` is used), and `outcome_sound` of any report whose error is set whenever
  `runProgramWith`'s is.
- `type_goal_inhabited`: if the goal is proved and is the type `t`,
  there is a valuation `ρ` with one value per entry of `out.entries`,
  satisfying the final scope if it is untainted and, by its first
  values, the scope at the `qed` (`ProvedAt`), under which `t`
  evaluates to a value `V` that has type `Type()`, and some value has
  type `V`, both by `out.sigs` closed by `ρ`.
- `fn_goal_holds`: if the goal is proved and is the function goal with
  telescopes `ps` and `rs`, there is a valuation `ρ` as in
  `type_goal_inhabited` such that `out.qedFn` names a function `d` of
  `out.fns`, and every list of values satisfying `ps` under `ρ` is
  followed by values satisfying `rs`, to which `d`, run on any
  run-time arguments related to the former by `ps`'s multiplicities,
  returns run-time results related by `rs`'s multiplicities.
- `no_empty_goal`: if the program declares a data type with no value
  constructors and its `goal` is an application of it, the goal is not
  reported proved.
- `run_sound` and `run_no_empty_goal`: `runProgram_sound` and
  `no_empty_goal` for `run source phase`.
- `reached_eval_ok` and `reached_run_ok`: at any state that checking a
  program reaches with any table (`checkItems`), an expression checked
  there as `print`, a `comptime` pattern `let` and `qed` against a type
  goal check theirs (`closed`, `checkExpr` under `TopState.ctx` with
  the item's `place`, given nothing or the goal's type), with one
  untainted result, has an evaluation by the relation (`Eval`) to one
  run-time value, related by `Rel` to an ideal value that has a type
  under a valuation satisfying the state's scope, and the top level's
  evaluation (`TopState.eval`) returns that value. A statement checked
  there as the top level checks one, leaving the scope untainted, has
  a run (`EvalStmt`), the one `TopState.run` gives.

The evaluator is defined only for what has an evaluation: `evalExpr`
takes the fact that one exists and returns it, unique by determinism
(`Eval.det`), so it neither fails nor runs without end. Outside the
solving pass, `topItem` evaluates with that fact from `TopState.Runs`,
which holds at every state `topItems` reaches by `TopInv.runs`, the
main lemma applied to the item; the solving pass evaluates nothing.
Every definition is total, by structural or well-founded recursion,
with no fuel, which is what the gate checks, so checking and evaluating
a program is meant to end, by Lean's acceptance of those definitions. The top level does not evaluate a `qed`'s expression:
its value is shown nowhere, and `reached_eval_ok` says its evaluation
exists and is what `TopState.eval` would return.

`tests/Audit.lean` prints the axioms these use. `Sound/Top.lean` has
`#guard`s showing that the goal clause is reached by small
programs: phase 1 programs with a recursive function and a `match`,
against a type goal and against a function goal; a program with
`sorry` whose goal is proved without relying on it; and a phase 2
program with `sorry` and erased fields. Its `#guard`s also show that,
in phases 1 and 2, a goal tainted through its type, a goal after a
top-level pattern `let` on `sorry`, and an empty type's goal met by
`qed sorry(_);` are not proved. Of the 449 programs of the
differential corpus, 45 report their goal proved.

## What has to be trusted

- Lean's kernel, and the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- The definitions the theorems are stated with: `Value`, `Term.eval`,
  `HasType`, `TeleSat`, `WType`, `WSat`, `Sat`, `junkHead`, `Approx`,
  `Sigs.erasedArg`, `Rel`, `MultRel`, `MultsRel`, `Sig.close`,
  `GoalHolds`, `GoalBelow`, `ProvedAt`, `World`,
  the evaluation relation `Eval` and its companions, `CallRel` among
  them, and the meaning of `runProgram`, `run`, `checkItems`,
  `topItems`, `TopState.eval`, `TopState.run` and `Outcome`'s fields. That `HasType` captures
  what a value of a type is rests on SOUNDNESS.md part 2, which it
  follows; that `Rel` and `Approx` capture what erasure and taint may
  remove rests on a reading of §12 and §16.
- That the Lean checker implements DESIGN.md. Nothing proves this; it is
  supported only by the differential comparison, in which the two
  implementations agree on whether there is an error, the printed
  values, `qed`, `goalProved` and `containsSorry` for every program of
  the corpus.
- The parser: no theorem is about it. The `run_` theorems say nothing
  about whether the parsed program is the program the source text
  means.
- Nothing is proved about the TypeScript implementation.

## How it differs from the TypeScript implementation

These are choices Claude sessions made, recorded in ASSUMPTIONS.md
items 69 to 75.

- **Canonicalization takes one pass.** When an entry gets a rule, every
  other rule is rewritten by it at once (`addRule`), so rules' terms
  mention no entry that has a rule.
- **Results are terms.** An application written in an expression gets
  no entry of its own; its result is the application term, which §7's
  entry would canonicalize to.
- **Evaluation is a relation, run where it has a derivation.**
  Evaluation is the relation `Eval`, with no measure and no
  termination check. The evaluator follows it and is defined only for
  what has an evaluation, which the top level knows from the soundness
  proof; the pass that solves `_` evaluates nothing. There is no fuel.
- **Internal checks.** Where the TypeScript checker relies on
  invariants of its data, the Lean checker tests them and rejects the
  program with an error starting "internal:", so that the proofs need
  no syntactic invariants: a term with no type, a head with no
  signature, an expression producing no value, a `_` with no entry, a
  term to abstract that is not closed (`abstract?`), an argument with
  no parameter, an undetermined entry in a whole telescope, a missing
  `subterm` parameter or argument in a decrease check, forcing that
  gets stuck (no type for the scrutinee or a term, an equation that is
  not canonical, an entry not in scope, an equation no entry can take a
  rule from), a value constructor that was not forced, an annotation
  mentioning an entry created after the scrutinee, a `comptime` pattern
  `let` below the top level, a `removed` expression being checked, and
  a telescope, value-constructor return or goal mentioning an entry
  below the top level, a value-constructor return that does not apply
  its type constructor, and a type constructor or value constructor
  named `sorry`, which, `sorry` being a keyword, the parser is believed
  never to produce. No program of the corpus reaches one of these;
  nothing proves them unreachable.
- It has no interface: it answers `inspect;` as text, and nothing else
  of §13.

## What is not proved

- Anything about `solveFrom`: that it finds a term for every `_`
  DESIGN.md means to be solved, or the terms DESIGN.md means. The
  theorems hold for `runProgramWith` with any table, so a wrong table
  is believed to cost only completeness (a program rejected), not
  soundness.
- That the internal checks are unreachable on programs DESIGN.md
  accepts.
- That `reached_eval_ok` and `reached_run_ok` describe every evaluation
  the top level performs: they are about the checks `print`, a
  `comptime` pattern `let` and the other top-level statements perform
  before evaluating; the link to those items is by reading `topItem`.
- That `runProgram` reports the error of the first item that fails:
  it relies on `solveFrom`, which evaluates nothing, meeting the same
  errors as `runProgramWith` up to the first error found by
  evaluating.
- That the Lean checker implements DESIGN.md, that the parser reads
  the source as DESIGN.md means it, and anything about the TypeScript
  code (see above).

One thing about how the statements read: `GoalHolds` for a function
goal says that every tuple of values satisfying the goal's parameters
has results. When no values satisfy the parameters it holds with
nothing to show, as an implication from a false hypothesis does; that
is what a function goal states, not a gap in the theorem.
