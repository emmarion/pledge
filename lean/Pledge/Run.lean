import Pledge.Sound.Item
import Pledge.Solve

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
  topItems (.init phase table) (.init phase table) prog

def runProgramWith (phase : Nat) (table : Table) (prog : Program) (has : String → Bool)
    (syntaxError : Option (Pos × String) := none) : Outcome :=
  let (st, failed) := checkItems phase table prog
  outcome has st failed syntaxError

/-- The error reported when checking stops at `(e, t, n)` at the state `st` before `t`: the solver's, when `e` was not
found by evaluating and the solver, solving `t` from `st`, stops at an error that is not internal; otherwise `e`. -/
def report (st : TopState) : Stop → Stop
  | (e, t, n) => (if e.evaluated then e else match Solve.item st t with
    | .error (.failed e') => if e'.internal then e else e'
    | _ => e, t, n)

/-- Extends the table until checking with it needs no more (§20): when checking stops at an error not found by
evaluating, the solver solves the item it stopped at, from the state before it, and the terms it finds for `_` the
table had none for are added. -/
def solveTable (phase : Nat) (prog : Program) (table : Table) : Table :=
  match checkItems phase table prog with
  | (st, some (e, t, _)) =>
    match e.evaluated, Solve.item st t with
    | false, .error (.solved new) =>
      if _h : unsolved prog (table ++ new) < unsolved prog table then solveTable phase prog (table ++ new) else table
    | _, _ => table
  | (_, none) => table
termination_by unsolved prog table

/-- The table for the program's `_` that solving ends with. -/
def solution (phase : Nat) (prog : Program) : Table := solveTable phase prog []

/-- Checks and evaluates a parsed program with the table solving ends with, its error as `report` gives it. -/
def runProgram (phase : Nat) (prog : Program) (has : String → Bool)
    (syntaxError : Option (Pos × String) := none) : Outcome :=
  let (st, failed) := checkItems phase (solution phase prog) prog
  outcome has st (failed.map (report st)) syntaxError

/-- Parses, checks and evaluates a program under a phase. -/
def run (source : String) (phase : Nat) : Outcome :=
  let (prog, err) := parse source phase
  runProgram phase prog (hasKeyword source phase) err

end Pledge
