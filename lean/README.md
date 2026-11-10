# The Lean implementation

A second implementation of Pledge's checker and evaluator, in Lean 4
with no library beyond Lean's core, together with soundness theorems
that Lean checks for phase 1 programs without `sorry`. Claude sessions
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
  `Term.eval`, `HasType`, `TeleSat`, `Sat`, `Sig.close`.
- `Pledge/Unify.lean`: opening telescopes, `abstract?`, the strict
  subterm relation, `difference` (§12), and the equation solver behind
  forcing (§7) and `_` arguments (§16).
- `Pledge/Eval.lean`: the evaluator (§11) and its measure.
- `Pledge/Check/Basic.lean`, `Expr.lean`, `Top.lean`: the checker;
  `Top.lean` has `runProgram`, `run` and `Outcome`.
- `Main.lean`: the command line.
- `Pledge/CoreLemmas.lean`, `UnifySound.lean`, `Pledge/Sound/`: the
  proofs. `Sound/Plain.lean` defines `Program.plain`, `Sound/Defs.lean`
  the invariants and `GoalHolds`, and `Sound/Top.lean` the headline
  theorems.
- `Pledge/ParserTest.lean`, `EvalTest.lean`, `UnifyTest.lean`: `#guard`
  tests.
- `tests/`: the differential comparison with the TypeScript checker
  (`tests/README.md`), `Audit.lean` and `gate.mjs`.

## What Lean checks

A program is **plain** (`Program.plain`) when it contains no `sorry`,
no written multiplicity and no `removed` node; for a phase 1 program
the parser produces, this is meant to mean that it contains no
`sorry`. For a plain program `prog`, any `has` (what the source is
taken to contain, which `run` reads off the tokens) and any syntax
error `err`, writing `out` for `runProgram 1 prog has err`, Lean checks:

- `runProgram_sound`: there is a world `W` whose closed signatures
  `W.Sc` are exactly `out.sigs.map (Sig.close W.ρ)`, whose functions
  are `out.fns`, and whose valuation `W.ρ` satisfies the final
  top-level scope (`Sat W.Sc out.entries W.ρ`); and if `out.goalProved
  = some true`, the goal `out.goal` holds in `W` (`GoalHolds`).
- `type_goal_inhabited`: if the goal is proved and is the type `t`, then
  for some valuation `ρ` satisfying the final scope, `t` evaluates to a
  type `V` and some value has type `V` by the program's signatures
  closed by `ρ`.
- `fn_goal_holds`: if the goal is proved and is the function goal with
  telescopes `ps` and `rs`, then for some valuation `ρ` satisfying the
  final scope, every list of values satisfying `ps` is followed by
  values satisfying `rs`.
- `no_empty_goal`: if the program declares a data type with no value
  constructors and its `goal` is an application of it, the goal is not
  reported proved.
- `run_sound` and `run_no_empty_goal`: the same for `run source 1`,
  given that the program `parse source 1` gives is plain.
- `reached_eval_ok` and `reached_run_ok`: at any state the checker
  reaches on a plain program, an expression or statement checked there
  at the top level evaluates without error, so the top level does not
  report "evaluation stopped" for it.

`tests/Audit.lean` prints the axioms these use. `Sound/Top.lean` has
`#guard`s showing that the goal clause is reached by small programs,
one with a recursive function and a `match`, and that a program whose
goal is an empty type proved by `qed sorry(_);` is not plain and not
proved. In the differential corpus, 25 phase 1 programs without
`sorry` report their goal proved.

## What has to be trusted

- Lean's kernel, and the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
- The definitions the theorems are stated with: `Value`, `Term.eval`,
  `HasType`, `TeleSat`, `Sat`, `Sig.close`, `GoalHolds`, `World`,
  `Program.plain`, and the meaning of `runProgram`, `run` and
  `Outcome`'s fields. That `HasType` captures what a value of a type is
  rests on SOUNDNESS.md part 2, which it follows.
- That the Lean checker implements DESIGN.md. Nothing proves this; it is
  supported only by the differential comparison, in which the two
  implementations agree on whether there is an error, the printed
  values, `qed`, `goalProved` and `containsSorry` for every program of
  the corpus.
- The parser: no theorem is about it. The `run_` theorems assume that
  the parsed program is plain and say nothing about whether it is the
  program the source text means.
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
- **The evaluator is total, with a dynamic termination check.** Each
  activation carries the measure of SOUNDNESS.md part 6; a call whose
  measure is not below its caller's is not made, and evaluation stops
  with the error "the call to … does not decrease", which the top
  level reports as "evaluation stopped". There is no fuel.
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
  below the top level. No program of the corpus reaches one of these
  or the evaluator's termination check; nothing proves them
  unreachable.
- It has no interface: it answers `inspect;` as text, and nothing else
  of §13.

## What is not proved

- Programs containing `sorry`, and so taint (§12): the theorems assume
  a plain program.
- Phase 2 and erasure (§16).
- That the internal checks and the evaluator's termination check are
  unreachable on programs DESIGN.md accepts. Under phase 2, a call that
  decreases only on an erased `subterm` parameter is stopped by the
  termination check, where the TypeScript implementation evaluates it
  (ASSUMPTIONS.md item 72).
- That checking terminates, as a theorem: every definition is total,
  defined by structural or well-founded recursion, with no `partial`
  and no fuel, which is what the gate checks; Lean accepts no
  definition it cannot show terminates.
- That `fn_goal_holds`'s returns are computed by the function the `qed`
  names: the proof goes through that function's specification, but the
  statement only says that returns exist.
- That `reached_eval_ok` and `reached_run_ok` cover every evaluation:
  they are about evaluations after an item's checking succeeds, as
  `print`, `qed`, `let` and `comptime` pattern `let` perform them; the
  link to those items is by reading `topItem`, not by a theorem about
  `Outcome.error`.
