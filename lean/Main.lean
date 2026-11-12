import Pledge

open Pledge

def jsonString (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat < 0x20 then
      let h := (Nat.toDigits 16 c.toNat)
      "\\u" ++ String.ofList (List.replicate (4 - h.length) '0' ++ h)
    else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

def jsonList (items : List String) : String := "[" ++ ", ".intercalate items ++ "]"

def jsonPositioned (key : String) (items : List (Pos × String)) : String :=
  jsonList (items.map fun (p, s) => s!"\{\"pos\": {p}, \"{key}\": {jsonString s}}")

def Pledge.Outcome.json (o : Outcome) : String :=
  let error := match o.error with
    | none => "null"
    | some (p, m) => s!"\{\"pos\": {p}, \"message\": {jsonString m}}"
  let proved := match o.goalProved with
    | none => "null"
    | some b => toString b
  s!"\{\"error\": {error}, \"prints\": {jsonPositioned "value" o.prints}, \"qed\": {jsonString o.qed}, " ++
    s!"\"goalProved\": {proved}, \"containsSorry\": {o.containsSorry}, " ++
    s!"\"inspects\": {jsonPositioned "text" o.inspects}}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", "--phase", n, file] =>
    match n.toNat? with
    | some phase =>
      IO.println (run (← IO.FS.readFile file) phase).json
      pure 0
    | none => IO.eprintln s!"not a phase: {n}"; pure 2
  | _ => IO.eprintln "usage: pledge check --phase N FILE"; pure 2
