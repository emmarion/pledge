
export type Phase = 1 | 2;

export interface Span { start: number; end: number }

export interface Id { name: string | null; span: Span }

export interface Term { head: Id; args: Term[] | null; span: Span }

export type Mult = "many" | "erased";

export type Ann =
  | { kind: "type"; term: Term }
  | { kind: "is"; term: Term };

export interface Binder { name: Id; ann: Ann; mult: Mult | null; span: Span }

export interface Param extends Binder { subterm: boolean }

export interface LetBinder { name: Id; ann: Ann | null; mult: Mult | null; span: Span }

export interface Pattern { ctor: Id; fields: Id[]; span: Span }

export type Mark = "subterm" | "same";
export interface Arg { mark: Mark | null; expr: Expr; span: Span }

export type Tele = Binder[] | "_";

export interface Branch { pat: Pattern; body: Expr; span: Span }

export type Expr =
  | { kind: "var"; name: Id; span: Span }
  | { kind: "app"; head: Id; args: Arg[]; span: Span }
  | { kind: "tuple"; elems: Expr[]; span: Span }
  | { kind: "block"; stmts: Stmt[]; final: Expr; span: Span }
  | { kind: "match"; mult: Mult | null; scrut: Expr; ann: Tele; branches: Branch[]; span: Span }
  | { kind: "sorry"; tele: Tele; span: Span };

export type Stmt =
  | { kind: "let"; binders: LetBinder[]; rhs: Expr; span: Span }
  | { kind: "patlet"; comptime: boolean; mult: Mult | null; pat: Pattern; rhs: Expr; span: Span }
  | { kind: "inspect"; span: Span };

export interface TypedParam { name: Id; type: Term; span: Span }

export interface Ctor { name: Id; fields: Binder[]; ret: Term; span: Span }

export interface Data { kind: "data"; name: Id; params: TypedParam[]; ctors: Ctor[]; span: Span }

export interface Fn { kind: "fn"; name: Id; params: Param[]; returns: Binder[]; body: Expr & { kind: "block" }; span: Span }

export type Top =
  | Data
  | Fn
  | { kind: "mutual"; decls: Data[] | Fn[]; span: Span }
  | Stmt
  | { kind: "print"; expr: Expr; span: Span }
  | { kind: "goal"; type: Term; span: Span }
  | { kind: "qed"; expr: Expr; span: Span };

export interface Program { tops: Top[]; span: Span }
