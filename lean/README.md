# The Lean implementation

A second implementation of Pledge's checker and evaluator, in Lean 4
with no library beyond Lean's core, together with soundness theorems
that Lean checks for programs without `_` arguments, under any phase,
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
`skipKernelTC` or anything named like fuel, `partial` being allowed
only on the five declarations of the evaluator in `Pledge/Eval.lean`,
which must all be there; runs `tests/Audit.lean`,
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
  forcing (§7) and `_` arguments (§16).
- `Pledge/Eval.lean`: evaluation (§11, §12, §16) as a big-step
  relation, `Eval` with `EvalList`, `CallRel`, `EvalBlock` and
  `EvalStmt`; its determinism (`Eval.det`) and monotonicity in the
  program (`Eval.ext`); and the executable evaluator, `evalExpr` and
  its companions, whose results carry a derivation of the relation.
- `Pledge/Check/Basic.lean`, `Expr.lean`, `Top.lean`: the checker;
  `Top.lean` has `runProgram`, `run` and `Outcome`.
- `Main.lean`: the command line.
- `Pledge/CoreLemmas.lean`, `UnifySound.lean`, `Pledge/Sound/`: the
  proofs. `Sound/HoleFree.lean` defines `Program.holeFree`;
  `Sound/Defs.lean` worlds, the invariants, the function
  specifications and `GoalHolds`; `Sound/Measure.lean` the measure of
  SOUNDNESS.md part 6 that the totality proof inducts on;
  `Sound/Expr.lean` the main lemma, `Expr.sound` and `Stmt.sound`, by
  one lemma per construct, whose proofs are mostly in
  `Sound/Simple.lean`, `Call.lean`, `Match.lean` and `Erased.lean`;
  `Sound/Fn.lean` and `Data.lean` the declaration groups, and
  `Data.lean` the `goal` item; `Sound/Stmt.lean` the other top-level
  statements; and `Sound/Top.lean` the headline theorems.
- `Pledge/ParserTest.lean`, `EvalTest.lean`, `UnifyTest.lean`: `#guard`
  tests.
- `tests/`: the differential comparison with the TypeScript checker
  (`tests/README.md`), `Audit.lean` and `gate.mjs`.

## The model the theorems use

The theorems relate two kinds of value. An **ideal valuation** gives
each entry of a scope a value, as the valuation of SOUNDNESS.md part 3
does, and values are typed (`HasType`) by the program's signatures
closed by the ideal values of the top-level entries they mention
(`Sig.close`). **Run-time values** are what the evaluation relation
computes, with `removed` where taint or erasure removed code (§12,
§16). At a position that is not erased, a run-time value is related to
an ideal one by `Rel`: the same head, and each argument related in the
same way, except an erased argument, which only approximates
(`Approx`: `removed`, or the same head over approximating arguments).
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

A program is **hole-free** (`Program.holeFree`, `Sound/HoleFree.lean`)
when no expression in it is `_` (§16's `_` arguments). `sorry`, `_` in
place of a telescope, as in `sorry(_)`, and multiplicities are allowed.
For a hole-free program `prog`, any phase, any `has` (whether the
source is taken to contain a keyword, an argument of `runProgram` with
no default, which `run` reads off the tokens) and any syntax error
`err`, writing `out` for
`runProgram phase prog has err`, Lean checks:

- `runProgram_sound`: there is a world `W` whose evaluator's view of
  the program `W.P` is that of the final top-level state, whose closed
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
  `no_empty_goal` for `run source phase`, given that the program
  `parse source phase` gives is hole-free.
- `reached_eval_ok` and `reached_run_ok`: at any state the checker
  reaches on a hole-free program, while its scope is untainted, an
  expression checked there at the top level, outside an erased
  position, with an untainted result, and given nothing or closed types
  of multiplicity `many` with no `is` clause, as `print`, `qed` against
  a type goal and a `comptime` pattern `let` check theirs, has an
  evaluation by the relation (`Eval`) to one run-time value, related
  by `Rel` to an ideal
  value that has a type under a valuation satisfying the state's scope;
  any value the top level's evaluation (`TopState.eval`) returns for it
  is that one. A statement checked there that leaves the scope
  untainted has a run (`EvalStmt`).

The theorems speak of evaluation as the relation. The executable
evaluator is `partial`, so no theorem can say what it does; what links
it to the theorems is its result type: each value or environment it
returns comes with a derivation of the relation, which
`TopState.eval_cert` and `TopState.run_cert` extract, and by
determinism (`Eval.det`) that is the result the theorems describe.

`tests/Audit.lean` prints the axioms these use. `Sound/Top.lean` has
`#guard`s showing that the goal clause is reached by small hole-free
programs: phase 1 programs with a recursive function and a `match`,
against a type goal and against a function goal; a program with
`sorry` whose goal is proved without relying on it; and a phase 2
program with `sorry` and erased fields. Its `#guard`s also show that,
in phases 1 and 2, a goal tainted through its type, a goal after a
top-level pattern `let` on `sorry`, and an empty type's goal met by
`qed sorry(_);` are not proved. Of the 351 programs of the
differential corpus, 305 are hole-free, and 30 of these report their
goal proved: 25 phase 1 programs without `sorry`, 3 phase 1 programs
with `sorry` and 2 phase 2 programs.

## What has to be trusted

- Lean's kernel, and the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- The definitions the theorems are stated with: `Value`, `Term.eval`,
  `HasType`, `TeleSat`, `WType`, `WSat`, `Sat`, `junkHead`, `Approx`,
  `Sigs.erasedArg`, `Rel`, `MultRel`, `MultsRel`, `Sig.close`,
  `GoalHolds`, `GoalBelow`, `ProvedAt`, `World`, `Program.holeFree`,
  the evaluation relation `Eval` and its companions, `CallRel` among
  them, and the meaning of `runProgram`, `run`, `topItems` and
  `Outcome`'s fields. That `HasType` captures
  what a value of a type is rests on SOUNDNESS.md part 2, which it
  follows; that `Rel` and `Approx` capture what erasure and taint may
  remove rests on a reading of §12 and §16.
- That the Lean checker implements DESIGN.md. Nothing proves this; it is
  supported only by the differential comparison, in which the two
  implementations agree on whether there is an error, the printed
  values, `qed`, `goalProved` and `containsSorry` for every program of
  the corpus.
- The parser: no theorem is about it. The `run_` theorems assume that
  the parsed program is hole-free and say nothing about whether it is
  the program the source text means.
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
- **The evaluator is partial, its results certified.** Evaluation is
  the relation `Eval`, with no measure and no termination check; the
  executable evaluator follows it, is `partial`, and returns each
  result with a derivation of the relation. It fails, and the top level
  reports "evaluation stopped", where no rule applies (an unbound name,
  no branch, a `removed` value inspected, `sorry` reached, a count
  mismatch); a run that does not end leaves checking without an end.
  There is no fuel.
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
  below the top level, and a type constructor or value constructor
  named `sorry`, which, `sorry` being a keyword, the parser is believed
  never to produce. No program of the corpus reaches one of these;
  nothing proves them unreachable.
- It has no interface: it answers `inspect;` as text, and nothing else
  of §13.

## What is not proved

- Programs with `_` arguments (§16): every theorem assumes a hole-free
  program, so the solving of `_` arguments by unification, and taint
  through a `_` (§12), are not covered.
- That the internal checks are unreachable on programs DESIGN.md
  accepts.
- Anything about the executable evaluator beyond its results'
  certificates: that it terminates, and that it does not fail, on the
  programs the theorems cover. The theorems say that an evaluation by
  the relation exists; that the `partial` function finds it is not
  established.
- That checking terminates: every definition other than the evaluator's
  five is total, defined by structural or well-founded recursion, with
  no fuel, which is what the gate checks; checking a program ends if
  each evaluation it performs does.
- That `reached_eval_ok` and `reached_run_ok` cover every evaluation:
  they are about evaluations after an item's checking succeeds, as
  `print`, `qed`, `let` and `comptime` pattern `let` perform them; the
  link to those items is by reading `topItem`, not by a theorem about
  `Outcome.error`.
- That the Lean checker implements DESIGN.md, that the parser reads
  the source as DESIGN.md means it, and anything about the TypeScript
  code (see above).

The statements are also weaker than they may first read:

- `GoalHolds` for a function goal is vacuous when no values satisfy
  the goal's parameters, which seems inherent in a statement of this
  shape.
