import Pledge.Sound.Item

namespace Pledge

/-- Checks the items in order, stopping at the first error: the state before it, and the error with its item and the
number of items after it. Each state is one the top level reaches (`TopOk`), so what it evaluates has an evaluation
(`TopState.Runs`). -/
def topItems (st : TopState) (h : TopOk st) : List Top → TopState × Option Stop
  | [] => (st, none)
  | t :: ts => match certify (topItem st h.runs t) with
    | .ok ⟨st', ht⟩ => topItems st' (h.next ht) ts
    | .error e => ({ st with snaps := st.snaps ++ e.snaps }, some (e, t, ts.length))

/-- Checks the items of a program under a phase from the initial state, given a table for its `_` (§20). -/
abbrev checkItems (phase : Nat) (table : Table) (prog : Program) : TopState × Option Stop :=
  topItems (.init phase table) (.init phase table false) prog

def runProgramWith (phase : Nat) (table : Table) (prog : Program) (has : String → Bool)
    (syntaxError : Option (Pos × String) := none) : Outcome :=
  let (st, failed) := checkItems phase table prog
  outcome has st failed syntaxError

def solveFrom (phase : Nat) (prog : Program) (table : Table) : Table × Option Stop :=
  match topItems (.init phase table true) (.init phase table true) prog with
  | (_, some (e, t, n)) =>
    if e.solved.isEmpty then (table, some (e, t, n))
    else if _h : unsolved prog (table ++ e.solved) < unsolved prog table then solveFrom phase prog (table ++ e.solved)
    else (table, some ({ e with msg := fun _ => "internal: a `_` was solved again; the checker rejects the program" },
      t, n))
  | (_, none) => (table, none)
termination_by unsolved prog table

def solution (phase : Nat) (prog : Program) : Table := (solveFrom phase prog []).1

/-- Checks and evaluates a parsed program: finds the solutions of its `_` (§20), which evaluates nothing, then checks
and evaluates it with them, reporting what that reports. Solving gives only the text of an error, when it failed at
the same item with an error not found by evaluating; an error it did not meet there is reported as internal. -/
def runProgram (phase : Nat) (prog : Program) (has : String → Bool)
    (syntaxError : Option (Pos × String) := none) : Outcome :=
  let (table, solving) := solveFrom phase prog []
  let (st, failed) := checkItems phase table prog
  outcome has st failed syntaxError fun (e, _, n) =>
    if e.evaluated then (e.pos, e.msg ()) else match solving.filter (·.2.2 == n) with
      | some (e', _) => (e'.pos, e'.msg ())
      | none => (e.pos, s!"internal: the solutions found for `_` do not check: {e.msg ()}")

/-- Parses, checks and evaluates a program under a phase. -/
def run (source : String) (phase : Nat) : Outcome :=
  let (prog, err) := parse source phase
  runProgram phase prog (hasKeyword source phase) err

end Pledge
