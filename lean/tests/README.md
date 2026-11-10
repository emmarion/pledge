# Differential tests

`corpus.json` records what the TypeScript checker (`src/check.ts`)
says about a set of programs, so that the Lean implementation's
verdicts can be compared with it. It is meant to hold every distinct
`(source, phase)` pair that the TypeScript test suite passes to
`check`, every `tests/*.pledge` file (phase 2 for `phase2_*`, else 1),
and each tutorial page's read-only boxes joined with its starting text
and with its solution (ASSUMPTIONS.md item 22). Each program has an
`origin` (the test file and line of the call, the `.pledge` file, or
`tutorial/<slug>/initial|solution`) and the checker's `expected`
verdict: `error` (`null` or `{pos, message}`), `prints`, `qed`,
`goalProved`, `containsSorry`, and `inspects`, whose `text` is the
Scope panel's entries, one per line.

## Regenerating

From the repository root, with Node 22.18 or later (it runs the
TypeScript sources directly):

```sh
node lean/tests/gen-corpus.mjs
```

It copies the repository to a temporary directory, patches the copy's
`src/check.ts` to log each call, runs the test suite there, and
deletes the copy; `src/` itself is not changed.

## Comparing

```sh
node lean/tests/compare.mjs [--phase1-only] [--filter TEXT] [--verbose] [--exe PATH]
```

It runs `lean/.lake/build/bin/pledge check --phase N FILE` (or the
executable given by `--exe` or `PLEDGE_EXE`) on each program, which is
meant to print one JSON object of the same shape as `expected`. The
two must agree on whether there is an error, the printed values in
order, `qed`, `goalProved` and `containsSorry`; error positions and
messages, print positions and inspect positions are only counted as
informational differences (`--verbose` lists them). `--filter` keeps
programs whose origin or source contains the text. Each disagreement
is printed with both verdicts and the path of a file holding the
source, and the exit code is then non-zero.

`ts-pledge.mjs` puts the TypeScript checker behind the same command
line, so `node lean/tests/compare.mjs --exe lean/tests/ts-pledge.mjs`
checks the comparison itself; every program should agree.
