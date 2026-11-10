import Pledge.Syntax

namespace Pledge

/-- Why lexing stopped; the message is built only when the error is reported. -/
inductive LexError where
  | nonAscii (c : Char)
  | notName (word : String)
  | unexpected (c : Char)
  deriving BEq, Repr

def LexError.message : LexError → String
  | .nonAscii c => s!"non-ASCII character \"{c}\"; source text is ASCII"
  | .notName w => if w.all Char.isDigit then s!"`{w}` is not a name, and Pledge has no literals (§15)"
    else s!"`{w}` is not a name: a name starts with a letter (§1)"
  | .unexpected c => s!"unexpected character \"{c}\""

inductive Kind where
  | name | keyword | punct | underscore | eof
  | error (e : LexError)
  deriving BEq, Repr

structure Token where
  kind : Kind
  text : String
  pos : Pos
  deriving Repr

def phase2Mults : List String := ["erased", "many"]

def keywords (phase : Nat) : List String :=
  ["comptime", "data", "fn", "goal", "inspect", "is", "let", "match", "mutual", "print", "qed", "same", "sorry",
    "subterm"] ++ if phase ≥ 2 then phase2Mults else []

private def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

private def isSpace (c : Char) : Bool := c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)

private def wordKind (reserved : List String) (w : String) : Kind :=
  if w == "_" then .underscore
  else if !(w.front.isAlpha) then .error (.notName w)
  else if reserved.contains w then .keyword else .name

/-- Lexes the characters from offset `p`; `word` is the start and text of the word being read, and `comment`
says whether a comment is being skipped. The result ends with a token of kind `eof` or `error`. -/
private def lexFrom (reserved : List String) (word : Option (Pos × String)) (comment : Bool) :
    Pos → List Char → List Token
  | p, [] => [⟨.eof, "", p⟩]
  | p, c :: cs =>
    if c.toNat > 0x7f then [⟨.error (.nonAscii c), "", p⟩]
    else if comment then lexFrom reserved none (c != '\n') (p + 1) cs
    else if isWordChar c then
      let (start, w) := word.getD (p, "")
      let w := w.push c
      if cs.head?.any isWordChar then lexFrom reserved (some (start, w)) false (p + 1) cs
      else match wordKind reserved w with
        | .error e => [⟨.error e, "", start⟩]
        | k => ⟨k, w, start⟩ :: lexFrom reserved none false (p + 1) cs
    else if isSpace c then lexFrom reserved none false (p + 1) cs
    else match c, cs with
      | '-', '-' :: rest => lexFrom reserved none true (p + 2) rest
      | '=', '>' :: rest => ⟨.punct, "=>", p⟩ :: lexFrom reserved none false (p + 2) rest
      | '-', '>' :: rest => ⟨.punct, "->", p⟩ :: lexFrom reserved none false (p + 2) rest
      | c, rest => if "(){},;:=".contains c then ⟨.punct, c.toString, p⟩ :: lexFrom reserved none false (p + 1) rest
        else [⟨.error (.unexpected c), "", p⟩]
termination_by _ cs => cs.length

/-- The tokens of `source` under `phase`, ending with one of kind `eof` or `error`
(`erased` and `many` are keywords only from phase 2 on). -/
def lex (source : String) (phase : Nat) : List Token :=
  lexFrom (keywords phase) none false 0 source.toList

def hasKeyword (source : String) (phase : Nat) (word : String) : Bool :=
  (lex source phase).any fun t => t.kind == .keyword && t.text == word

end Pledge
