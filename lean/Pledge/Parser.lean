import Pledge.Lexer

namespace Pledge.Parser

/-- A syntax error at a token; the message is built only when the error is reported. -/
structure Err where
  tok : Token
  msg : Unit → String

/-- The tokens still to parse, at most `b` of them, and the token of kind `eof` or `error` after them. -/
structure St (b : Nat) where
  toks : List Token
  last : Token
  le : toks.length ≤ b

abbrev M (b : Nat) := StateT (St b) (Except Err)

variable {b : Nat} {α : Type}

def peekAt (k : Nat) : M b Token := do let s ← get; pure (s.toks.getD k s.last)

def peek : M b Token := peekAt 0

def next : M b Token := fun
  | ⟨t :: r, l, h⟩ => .ok (t, ⟨r, l, Nat.le_of_succ_le h⟩)
  | s => .ok (s.last, s)

def fail (t : Token) (msg : Unit → String) : M b α := throw ⟨t, msg⟩

def failHere (msg : Unit → String) : M b α := do fail (← peek) msg

def tokenText (t : Token) : String :=
  match t.kind with
  | .eof => "end of input"
  | .keyword => s!"keyword `{t.text}`"
  | _ => s!"`{t.text}`"

def expected (t : Token) (what : String) (rule := "") : M b α :=
  fail t fun _ => s!"expected {what}, found {tokenText t}" ++ if rule.isEmpty then "" else s!": {rule}"

def isText (t : Token) (text : String) : Bool := t.kind != .name && t.text == text

def see (text : String) : M b Bool := (isText · text) <$> peek

def eat (text : String) : M b Bool := do if ← see text then discard next; pure true else pure false

def expect (text : String) : M b Unit := do
  let t ← next
  unless isText t text do expected t s!"`{text}`"

/-- Runs `step` until it returns `none` or stops consuming tokens. -/
def many (step : M b (Option α)) : M b (List α) := go
where go (s : St b) : Except Err (List α × St b) := do
  match ← step s with
  | (some a, s') =>
    if s'.toks.length < s.toks.length then let (as, s'') ← go s'; pure (a :: as, s'') else pure ([a], s')
  | (none, s') => pure ([], s')
termination_by s.toks.length

/-- Consumes the next token and continues with `k` when it satisfies `p`. -/
def whenTok (p : Token → Bool) (k : Token → M b α) : M b (Option α) := do
  let t ← peek
  if p t then discard next; some <$> k t else pure none

def manyAfter (text : String) (item : M b α) : M b (List α) := many (whenTok (isText · text) fun _ => item)

def skipSemis : M b Unit := discard (manyAfter ";" (pure ()))

def endStatement : M b Unit := expect ";" *> skipSemis

def commaList (item : M b α) (close : String) (minOne : Bool) : M b (List α) := do
  if minOne || !(← see close) then pure ((← item) :: (← manyAfter "," item)) else pure []

def parensAfter (item : M b α) (minOne : Bool) : M b (List α) := commaList item ")" minOne <* expect ")"

def parens (item : M b α) (minOne : Bool) : M b (List α) := expect "(" *> parensAfter item minOne

def braces (item : M b α) : M b (List α) :=
  expect "{" *> many (do if ← see "}" then pure none else some <$> item) <* expect "}"

/-- Parses with `f`, after consuming the token `f` is given; `f` may parse with `fix f` again,
on the strictly shorter remainder, through its first argument. -/
def fix {n : Nat} (f : {c : Nat} → M c α → Token → M c α) : M n α := fun s =>
  match h : s.toks with
  | [] => f (fail s.last fun _ => "unexpected end of input") s.last s
  | t :: rest => do
    let (a, s') ← f (c := rest.length) (fun s' => fix f s') t ⟨rest, s.last, Nat.le_refl _⟩
    pure (a, ⟨s'.toks, s'.last, by have := s.le; have := s'.le; simp [h] at *; omega⟩)
termination_by s => s.toks.length
decreasing_by have := s'.le; simp [h]; omega

def nameOf (t : Token) : M b Name := if t.kind == .name then pure ⟨t.text, t.pos⟩ else expected t "a name"

def name : M b Name := next >>= nameOf

def id : M b Id := do
  let t ← next
  match t.kind with
  | .underscore => pure ⟨none, t.pos⟩
  | .name => pure ⟨some t.text, t.pos⟩
  | _ => expected t "a name or `_`"

def isMult (t : Token) : Bool := t.kind == .keyword && phase2Mults.contains t.text

def mult : M b (Option Mult) := whenTok isMult fun t => pure (if t.text == "erased" then .erased else .many)

def term : M b WTerm := fix fun term t => do
  let head ← nameOf t
  if ← see "(" then .app head <$> parens term false else pure (.var head)

def annOpt : M b (Option Ann) := do
  if ← eat ":" then (some ∘ .type) <$> term else if ← eat "is" then (some ∘ .is) <$> term else pure none

def letBinder (multOk : Bool) : M b LetBinder := do
  let m ← if multOk then mult else pure none
  let n ← id
  pure ⟨n, ← annOpt, m⟩

def binder (multOk : Bool) : M b Binder := do
  let ⟨n, ann, m⟩ ← letBinder multOk
  match ann with
  | some a => pure ⟨n, a, m⟩
  | none => do expected (← peek) "`:` or `is`" "a binder is written `name : T` or `name is e` (§1)"

def tele : M b (List Binder) := parens (binder true) true

def hole : M b Tele := (.hole ·.pos) <$> next

def param : M b Param := do pure ⟨← eat "subterm", ← binder true⟩

def field : M b Id := do
  let f ← id
  if ← see "(" then
    failHere fun _ => "a pattern does not nest: it names each field of one value constructor, with a name or `_` (§10)"
  pure f

def pattern : M b Pattern := do
  let t ← next
  if t.kind == .underscore then fail t fun _ =>
    "a branch is for one value constructor, written as a pattern such as `C(x, _)`; there is no catch-all branch (§10)"
  let ctor ← nameOf t
  unless ← see "(" do fail t fun _ =>
    s!"a pattern is written with its parentheses, even with no fields, as in `{ctor.name}()` (§1, §10)"
  pure ⟨ctor, ← parens field false⟩

def atPatLet : M b Bool := do
  let k := if isMult (← peek) then 1 else 0
  pure ((← peekAt k).kind == .name && isText (← peekAt (k + 1)) "(")

def patLet (pos : Pos) (comptime : Bool) (expr : M b Expr) : M b Stmt := do
  let m ← mult
  let pat ← pattern
  expect "="
  let rhs ← expr
  endStatement
  pure (.patlet pos comptime m pat rhs)

/-- A block statement or top-level `let` or `inspect`, after its first token `t`. -/
def stmtAfter (expr : M b Expr) (t : Token) : M b Stmt := do
  if isText t "inspect" then endStatement; return .inspect t.pos
  if ← atPatLet then return ← patLet t.pos false expr
  let binders ← if !isMult (← peek) && (← see "(") then parens (letBinder true) true
    else ([·]) <$> letBinder true
  expect "="
  let rhs ← expr
  endStatement
  pure (.let t.pos binders rhs)

def endsInBrace : Expr → Bool
  | .block .. | .match .. => true
  | _ => false

def blockAfter (expr : M b Expr) : M b Expr := do
  let stmts ← many (whenTok (fun t => isText t "let" || isText t "inspect") (stmtAfter expr))
  if ← see "}" then failHere fun _ => "a block ends with a final expression, after its statements (§8)"
  let final ← expr
  if endsInBrace final then skipSemis
  if ← see ";" then failHere fun _ => "a block ends with its final expression, which takes no `;` (§8)"
  expect "}"
  pure (.block stmts final)

def underPhase1 := ", and this program is checked under phase 1"

def arg (phase : Nat) (expr : M b Expr) : M b Arg := do
  let mark ← whenTok (fun t => isText t "subterm" || isText t "same") fun t =>
    pure (if t.text == "same" then Mark.same else .subterm)
  let t ← peek
  if t.kind != .underscore then return .mk mark (← expr)
  unless phase ≥ 2 do fail t fun _ =>
    s!"`_` stands for an erased argument only from phase 2 on (§16){underPhase1}"
  discard next
  pure (.mk mark (.var ⟨none, t.pos⟩))

/-- An expression, under `phase` (§19 `expr`). -/
def expr (phase : Nat) : M b Expr := fix fun expr t => do
  if t.kind == .name then
    return ← if ← see "(" then .app ⟨t.text, t.pos⟩ <$> parens (arg phase expr) false
      else pure (.var ⟨some t.text, t.pos⟩)
  match t.text with
  | "(" => .tuple t.pos <$> parensAfter expr true
  | "{" => blockAfter expr
  | "match" =>
    let m ← mult
    let scrut ← expr
    expect ":"
    let ann ← if (← peek).kind == .underscore then hole else .binders <$> tele
    let branches ← braces do
      let pat ← pattern
      expect "=>"
      let body ← expr
      endStatement
      pure (Branch.mk pat body)
    pure (.match t.pos m scrut ann branches)
  | "sorry" =>
    expect "("
    let after ← peekAt 1
    let tl ← if (← peek).kind == .underscore && !isText after ":" && !isText after "is" then hole
      else .binders <$> commaList (binder false) ")" true
    expect ")"
    pure (.sorry t.pos tl)
  | _ => expected t "an expression"

def data : M b Data := do
  let n ← name
  let params ← parens (do let i ← id; expect ":"; pure ⟨i, .type (← term), none⟩) false
  expect ":"
  let t ← next
  unless t.kind == .name && t.text == "Type" do expected t "`Type`"
  expect "("
  expect ")"
  let ctors ← braces do
    let c ← name
    let fs ← parens (binder true) false
    expect ":"
    let r ← term
    endStatement
    pure ⟨c, fs, r⟩
  skipSemis
  pure ⟨n, params, ctors⟩

def header : M b Header := do
  let params ← parens param false
  expect "->"
  unless ← see "(" do failHere fun _ => "a function's returns are a telescope, as in `-> (r : Nat())` (§8)"
  pure ⟨params, ← tele⟩

def fn (phase : Nat) : M b Fn := do
  let n ← name
  let h ← header
  expect "{"
  let body ← blockAfter (expr phase)
  skipSemis
  pure ⟨n, h, body⟩

def mutualAfter (phase : Nat) (pos : Pos) : M b Top := do
  expect "{"
  let t ← peek
  let top ← if isText t "data" then .mutualData pos <$> manyAfter "data" data
    else if isText t "fn" then .mutualFn pos <$> manyAfter "fn" (fn phase)
    else if isText t "}" then fail t fun _ => "a `mutual` block declares at least one `data` declaration or function"
    else expected t "`data` or `fn`"
  let u ← next
  if isText u "data" || isText u "fn" then
    fail u fun _ => "a `mutual` block holds either `data` declarations or functions, not both"
  unless isText u "}" do expected u "`data` or `fn`"
  skipSemis
  pure top

/-- A declaration or top-level statement, after its first token `t`. -/
def topAfter (phase : Nat) (t : Token) : M b Top := do
  let e := expr phase
  match t.kind, t.text with
  | .keyword, "data" => .data <$> data
  | .keyword, "fn" => .fn <$> fn phase
  | .keyword, "mutual" => mutualAfter phase t.pos
  | .keyword, "let" | .keyword, "inspect" => .stmt <$> stmtAfter e t
  | .keyword, "comptime" =>
    expect "let"
    unless ← atPatLet do fail t fun _ =>
      "`comptime` is written only on a pattern `let`, as in `comptime let C(x) = e;` (§11)"
    .stmt <$> patLet t.pos true e
  | .keyword, "print" => .print t.pos <$> e <* endStatement
  | .keyword, "goal" => .goal t.pos <$> (do if ← eat "fn" then .fn <$> header else .type <$> term) <* endStatement
  | .keyword, "qed" => .qed t.pos <$> e <* endStatement
  | _, _ => expected t "a declaration or a top-level statement"

/-- The items of the program up to the first error, and that error. -/
def program (phase : Nat) : M b (Program × Option Err) := fix fun program t =>
  if t.kind == .eof then pure ([], none) else
    tryCatch (do let top ← topAfter phase t; let (tops, e) ← program; pure (top :: tops, e))
      fun e => pure ([], some e)

/-- Where an error is reported and its message: a lexical error's own, or, under phase 1, a hint when the token
before the error is a name spelled as a multiplicity (§16). -/
def report (phase : Nat) (tokens : List Token) (e : Err) : Pos × String :=
  let hint := (tokens.filter (·.pos < e.tok.pos)).getLast?.filter fun p =>
    phase < 2 && p.kind == .name && phase2Mults.contains p.text
  match e.tok.kind, hint with
  | .error le, _ => (e.tok.pos, le.message)
  | _, some p => (p.pos, s!"`{p.text}` is a multiplicity, which phase 2 adds (§16){underPhase1}")
  | _, none => (e.tok.pos, e.msg ())

end Parser

/-- The items of `source` before its first syntax error under `phase`, and that error's position and message. -/
def parse (source : String) (phase : Nat) : Program × Option (Pos × String) :=
  let tokens := lex source phase
  match Parser.program phase ⟨tokens.dropLast, tokens.getLastD ⟨.eof, "", source.length⟩, Nat.le_refl _⟩ with
  | .ok ((tops, e), _) => (tops, e.map (Parser.report phase tokens))
  | .error e => ([], some (Parser.report phase tokens e))

end Pledge
