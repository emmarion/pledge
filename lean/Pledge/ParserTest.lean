import Pledge.Parser

namespace Pledge.ParserTest

def has (s frag : String) : Bool := (s.splitOn frag).length > 1

def ok (source : String) (phase := 1) : Bool := (parse source phase).2.isNone

def tops (source : String) (phase := 1) : Program := (parse source phase).1

def err (source : String) (pos : Pos) (frag : String) (phase := 1) : Bool :=
  match (parse source phase).2 with
  | some (p, m) => p == pos && has m frag
  | none => false

def nat := "data Nat() : Type() { Zero() : Nat(); Succ(pred : Nat()) : Nat(); }\n"

def phase1Files : List String := [
  include_str "../../tests/design_ack.pledge",
  include_str "../../tests/design_even_odd.pledge",
  include_str "../../tests/design_iszero.pledge",
  include_str "../../tests/design_let_is.pledge",
  include_str "../../tests/design_let_vcons.pledge",
  include_str "../../tests/design_reflection.pledge",
  include_str "../../tests/design_sorry.pledge",
  include_str "../../tests/design_vcons_application.pledge",
  include_str "../../tests/design_vhead.pledge",
  include_str "../../tests/design_vuncons.pledge"]

def phase2Files : List String := [
  include_str "../../tests/phase2_eq.pledge",
  include_str "../../tests/phase2_erased.pledge",
  include_str "../../tests/phase2_vec.pledge"]

#guard phase1Files.all fun f => ok f 1 && ok f 2
#guard phase2Files.all fun f => ok f 2

#guard match tops (include_str "../../tests/design_vhead.pledge") with
  | [.data _, .data _, .fn ⟨⟨"vhead", _⟩, ⟨[⟨false, ⟨⟨some "A", _⟩, .type (.app ⟨"Type", _⟩ []), none⟩⟩,
      ⟨false, ⟨⟨some "n", _⟩, .type (.app ⟨"Nat", _⟩ []), none⟩⟩,
      ⟨false, ⟨⟨some "v", _⟩, .type (.app ⟨"Vec", _⟩ [.var ⟨"A", _⟩, .app ⟨"Succ", _⟩ [.var ⟨"n", _⟩]]), none⟩⟩],
      [⟨⟨some "x", _⟩, .type (.var ⟨"A", _⟩), none⟩]⟩,
      .block [.patlet _ false none ⟨⟨"VCons", _⟩, [⟨none, _⟩, ⟨none, _⟩, ⟨some "hd", _⟩, ⟨none, _⟩]⟩
        (.var ⟨some "v", _⟩)] (.var ⟨some "hd", _⟩)⟩] => true
  | _ => false

#guard match tops (include_str "../../tests/design_ack.pledge") with
  | [_, .fn ⟨_, ⟨[⟨true, _⟩, ⟨true, _⟩], _⟩, .block [] (.match _ none _ _
      [.mk ⟨⟨"Zero", _⟩, _⟩ _, .mk ⟨⟨"Succ", _⟩, _⟩ (.match _ _ _ _ [_, .mk _
        (.app ⟨"ack", _⟩ [.mk (some .subterm) (.var ⟨some "m1", _⟩),
          .mk none (.app ⟨"ack", _⟩ [.mk (some .same) (.var ⟨some "m", _⟩),
            .mk (some .subterm) (.var ⟨some "n1", _⟩)])])])])⟩] => true
  | _ => false

#guard match tops (include_str "../../tests/design_even_odd.pledge") with
  | [_, .mutualData _ [⟨⟨"Even", _⟩, _, _⟩, ⟨⟨"Odd", _⟩, _, _⟩]] => true
  | _ => false

#guard match tops (include_str "../../tests/design_iszero.pledge") with
  | [_, _, .fn ⟨_, _, .block [] (.match _ _ _ _ [_, .mk _ (.match _ none (.var ⟨some "p", _⟩)
      (.binders [⟨⟨some "r", _⟩, .type (.app ⟨"Nat", _⟩ []), none⟩]) [])])⟩] => true
  | _ => false

#guard match (tops (include_str "../../tests/design_reflection.pledge")).getLast? with
  | some (.stmt (.patlet _ true none ⟨⟨"Some", _⟩, [⟨none, _⟩, ⟨some "p", _⟩]⟩
      (.app ⟨"decideEven", _⟩ [.mk none (.app ⟨"Succ", _⟩ [.mk none (.app ⟨"Succ", _⟩
        [.mk none (.app ⟨"Zero", _⟩ [])])])]))) => true
  | _ => false

#guard match tops s!"{nat}let y = sorry(x is Zero());" with
  | [_, .stmt (.let _ [⟨⟨some "y", _⟩, none, none⟩]
      (.sorry _ (.binders [⟨⟨some "x", _⟩, .is (.app ⟨"Zero", _⟩ []), none⟩])))] => true
  | _ => false

#guard match tops s!"{nat}goal Nat(); qed sorry(_); inspect; print (Zero(), x);" with
  | [_, .goal _ (.type (.app ⟨"Nat", _⟩ [])), .qed _ (.sorry _ (.hole _)), .stmt (.inspect _),
      .print _ (.tuple _ [.app ⟨"Zero", _⟩ [], .var ⟨some "x", _⟩])] => true
  | _ => false

#guard match tops "let (a, _ : Nat(), c is Zero()) = { inspect; match x : _ { Zero() => (y); } };" with
  | [.stmt (.let _ [⟨⟨some "a", _⟩, none, none⟩, ⟨⟨none, _⟩, some (.type (.app ⟨"Nat", _⟩ [])), none⟩,
      ⟨⟨some "c", _⟩, some (.is (.app ⟨"Zero", _⟩ [])), none⟩]
      (.block [.inspect _] (.match _ none (.var ⟨some "x", _⟩) (.hole _)
        [.mk ⟨⟨"Zero", _⟩, []⟩ (.tuple _ [.var ⟨some "y", _⟩])])))] => true
  | _ => false

#guard match (lex "let x = Zerö();" 1).getLast?, (lex "let x = 𝒳;" 1).getLast? with
  | some ⟨.error (.nonAscii _), _, 11⟩, some ⟨.error (.nonAscii _), _, 8⟩ => true
  | _, _ => false

#guard match tops "  let x = Zero(); -- c\nprint x;" with
  | [.stmt (.let 2 _ _), .print 23 _] => true
  | _ => false

#guard hasKeyword "let x = many;" 2 "many" && !hasKeyword "let x = many;" 1 "many" && !hasKeyword "-- let" 1 "let"

#guard ok s!"{nat};;fn f(n : Nat()) -> (r : Nat()) \{ let x = n;; \{ x }; };; let y = Zero();;;"
#guard ok "mutual { data A() : Type() {}; data B() : Type() { C() : B();; }; };"
#guard err ";" 0 "expected a declaration or a top-level statement, found `;`"
#guard err "let x = { y; };" 11 "a block ends with its final expression, which takes no `;`"

#guard [("let x = Zero()\nprint x;", 15, "expected `;`, found keyword `print`"),
  ("let x = ();", 9, "expected an expression, found `)`"),
  ("mutual { }", 9, "mutual"),
  ("mutual { data A() : Type() {} fn f() -> (r : A()) { r } }", 30, "either `data` declarations or functions"),
  ("let x = Zero(); -- café\n", 22, "non-ASCII"),
  ("let x = Zerö();", 11, "non-ASCII"),
  ("fn _(n : Nat()) -> (r : Nat()) { n }", 3, "expected a name, found `_`"),
  ("fn match(n : Nat()) -> (r : Nat()) { n }", 3, "keyword `match`"),
  ("let print = Zero();", 4, "keyword `print`"),
  ("data D(x is Zero()) : Type() {}", 9, "expected `:`"),
  ("data D() : Nat() {}", 11, "`Type`"),
  ("fn f() -> () { x }", 11, "a name or `_`"),
  ("fn f() { x }", 7, "`->`"),
  ("let x = 1;", 8, "`1` is not a name, and Pledge has no literals"),
  ("let x = _a;", 8, "`_a` is not a name: a name starts with a letter"),
  ("let x = a - b;", 10, "unexpected character"),
  ("let x = { comptime let C() = y; z };", 10, "an expression"),
  ("let x = f(_);", 10, "only from phase 2 on"),
  ("let x = { y; }", 11, "takes no `;`"),
  ("x;", 0, "a declaration or a top-level statement"),
  ("let x = ;\né", 8, "expected an expression"),
  ("let x = y;\né let", 11, "non-ASCII"),
  ("match x : _ {}", 0, "a declaration or a top-level statement"),
  ("let x = match y : _ { _ => y; };", 22, "no catch-all branch"),
  ("let x = match y : _ { C(D(z)) => y; };", 25, "does not nest"),
  ("let C = y; let x = match y : _ { C => y; };", 33, "with its parentheses"),
  ("comptime let x = y;", 0, "`comptime` is written only on a pattern `let`"),
  ("fn f(n : Nat()) -> r : Nat() { n }", 19, "returns are a telescope"),
  ("let x = { };", 10, "a block ends with a final expression"),
  ("let x = f(n", 11, "expected `)`, found end of input")].all fun (s, p, m) => err s p m

#guard match tops "let erased = many;" with
  | [.stmt (.let _ [⟨⟨some "erased", _⟩, none, none⟩] (.var ⟨some "many", _⟩))] => true
  | _ => false
#guard err "let x = many;" 8 "expected an expression, found keyword `many`" 2
#guard err "let erased = x;" 11 "expected a name or `_`, found `=`" 2
#guard ok "fn erased(many : Nat()) -> (r : Nat()) { many }"
#guard (parse "fn f(erased n : Nat()) -> (r : Nat()) { n }" 1).2 ==
  some (5, "`erased` is a multiplicity, which phase 2 adds (§16), and this program is checked under phase 1")

def phase2Program := s!"{nat}
data V(n : Nat()) : Type() \{ C(erased n : Nat(), many x : Nat()) : V(n); }
fn f(subterm erased n : Nat(), v : V(n)) -> (erased m : Nat(), r : Nat()) \{
  let erased C(k, x) = v;
  let (erased a : Nat(), many b) = match erased v : (erased s : Nat(), t : Nat()) \{ C(j, y) => (j, y); };
  let erased c = a;
  (c, b)
}
comptime let erased C(_, z) = C(Zero(), Zero());
let w = f(_, C(_, Zero()));
"

#guard ok phase2Program 2
#guard match tops phase2Program 2 with
  | [_, .data ⟨_, _, [⟨_, [⟨_, _, some .erased⟩, ⟨_, _, some .many⟩], _⟩]⟩,
      .fn ⟨_, ⟨[⟨true, ⟨_, _, some .erased⟩⟩, ⟨false, ⟨_, _, none⟩⟩], [⟨_, _, some .erased⟩, ⟨_, _, none⟩]⟩,
        .block [.patlet _ false (some .erased) _ _,
          .let _ [⟨_, _, some .erased⟩, ⟨_, _, some .many⟩]
            (.match _ (some .erased) _ (.binders [⟨_, _, some .erased⟩, ⟨_, _, none⟩]) _),
          .let _ [⟨⟨some "c", _⟩, _, some .erased⟩] _] _⟩,
      .stmt (.patlet _ true (some .erased) _ _),
      .stmt (.let _ [⟨⟨some "w", _⟩, none, none⟩] (.app ⟨"f", _⟩ [.mk none (.var ⟨none, _⟩),
        .mk none (.app ⟨"C", _⟩ [.mk none (.var ⟨none, _⟩), .mk none (.app ⟨"Zero", _⟩ [])])]))] => true
  | _ => false

#guard [("data D(erased n : Type()) : Type() {}", "keyword `erased`"),
  ("let x = sorry(erased y : Type());", "keyword `erased`"),
  ("let erased (x) = y;", "a name or `_`"),
  ("let x = (_);", "an expression")].all fun (s, m) => (parse s 2).2.any (has ·.2 m)

#guard match tops "goal fn (subterm n : Nat(), _ : Nat()) -> (r : Nat()); qed f;" with
  | [.goal _ (.fn ⟨[⟨true, ⟨⟨some "n", _⟩, .type (.app ⟨"Nat", _⟩ []), none⟩⟩,
      ⟨false, ⟨⟨none, _⟩, .type (.app ⟨"Nat", _⟩ []), none⟩⟩], [⟨⟨some "r", _⟩, _, none⟩]⟩),
      .qed _ (.var ⟨some "f", _⟩)] => true
  | _ => false
#guard match tops "goal fn () -> (erased r : Nat());" 2 with
  | [.goal _ (.fn ⟨[], [⟨⟨some "r", _⟩, _, some .erased⟩]⟩)] => true
  | _ => false
#guard [("goal fn f(n : Nat()) -> (r : Nat());", 8, "expected `(`, found `f`"),
  ("goal fn (n : Nat()) (r : Nat());", 20, "expected `->`"),
  ("goal fn (n : Nat()) -> (r : Nat()) { n }", 35, "expected `;`, found `{`"),
  ("goal fn (n : Nat()) -> ();", 24, "a name or `_`")].all fun (s, p, m) => err s p m

#guard (tops s!"{nat}let x = Zero();\nlet y = ;\nprint x;").length == 2

end Pledge.ParserTest
