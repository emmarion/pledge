import Pledge.Sound.Item

namespace Pledge

/-- Checks the items in order, stopping at the first error: the state before it, and the error with its item. Each
state is one the top level reaches (`TopOk`), so what it evaluates has an evaluation (`TopState.Runs`). -/
def topItems (st : TopState) (h : TopOk st) : List Top → TopState × Option (CheckError × Top)
  | [] => (st, none)
  | t :: ts => match certify (topItem st h.runs t) with
    | .ok ⟨st', ht⟩ => topItems st' (h.next ht) ts
    | .error e => ({ st with snaps := st.snaps ++ e.snaps }, some (e, t))

/-- Checks the items of a program under a phase from the initial state, given a table for its `_` (§20). -/
abbrev checkItems (phase : Nat) (table : Table) (prog : Program) : TopState × Option (CheckError × Top) :=
  topItems (.init phase table) (.init phase table false) prog

def runProgramWith (phase : Nat) (table : Table) (prog : Program) (has : String → Bool)
    (syntaxError : Option (Pos × String) := none) : Outcome :=
  let (st, failed) := checkItems phase table prog
  outcome has st failed syntaxError

def solveFrom (phase : Nat) (prog : Program) (table : Table) : Table × Option (CheckError × Top) :=
  match topItems (.init phase table true) (.init phase table true) prog with
  | (_, some (e, t)) =>
    if e.solved.isEmpty then (table, some (e, t))
    else if _h : unsolved prog (table ++ e.solved) < unsolved prog table then solveFrom phase prog (table ++ e.solved)
    else (table, some ({ e with msg := fun _ => "internal: a `_` was solved again; the checker rejects the program" },
      t))
  | (_, none) => (table, none)
termination_by unsolved prog table

def solution (phase : Nat) (prog : Program) : Table := (solveFrom phase prog []).1

/-- Checks and evaluates a parsed program: finds the solutions of its `_` (§20), which evaluates nothing, then checks
and evaluates it with them. An error met while solving is reported, unless checking with the solutions meets one
found by evaluating; any other error met only after solving is reported as internal. -/
def runProgram (phase : Nat) (prog : Program) (has : String → Bool)
    (syntaxError : Option (Pos × String) := none) : Outcome :=
  let (table, solving) := solveFrom phase prog []
  let (st, failed) := checkItems phase table prog
  outcome has st ((failed.filter (·.1.evaluated)).orElse fun _ => solving.orElse fun _ => failed.map fun (e, t) =>
    ({ e with msg := fun _ => s!"internal: the solutions found for `_` do not check: {e.msg ()}" }, t)) syntaxError

/-- Parses, checks and evaluates a program under a phase. -/
def run (source : String) (phase : Nat) : Outcome :=
  let (prog, err) := parse source phase
  runProgram phase prog (hasKeyword source phase) err

end Pledge
