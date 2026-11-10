export type Phase = 1 | 2;

export interface Span { start: number; end: number }

export interface Id { name: string | null; span: Span }

export interface Name { name: string; span: Span }

export interface WrittenTerm { head: Name; args: WrittenTerm[] | null; span: Span }

export type Mult = "many" | "erased";

export type Ann =
  | { kind: "type"; term: WrittenTerm }
  | { kind: "is"; term: WrittenTerm };

export interface WrittenBinder { name: Id; ann: Ann; mult: Mult | null; multStart: number; span: Span }

export interface Param extends WrittenBinder { subterm: boolean }

export interface LetBinder { name: Id; ann: Ann | null; mult: Mult | null; multStart: number; span: Span }

export interface Pattern { ctor: Name; fields: Id[]; span: Span }

export type Mark = "subterm" | "same";
export interface Arg { mark: Mark | null; expr: Expr; span: Span }

export type Tele = WrittenBinder[] | { kind: "_"; span: Span };

export interface Branch { pat: Pattern; body: Expr; span: Span }

export type Expr =
  | { kind: "var"; name: Id; span: Span }
  | { kind: "app"; head: Name; args: Arg[]; span: Span }
  | { kind: "tuple"; elems: Expr[]; span: Span }
  | { kind: "block"; stmts: Stmt[]; final: Expr; span: Span }
  | { kind: "match"; mult: Mult | null; multStart: number; scrut: Expr; ann: Tele; branches: Branch[]; span: Span }
  | { kind: "sorry"; tele: Tele; span: Span }
  | { kind: "removed"; span: Span };

export type Stmt =
  | { kind: "let"; binders: LetBinder[]; rhs: Expr; span: Span }
  | { kind: "patlet"; comptime: boolean; mult: Mult | null; pat: Pattern; rhs: Expr; span: Span }
  | { kind: "inspect"; span: Span };

export interface Ctor { name: Name; fields: WrittenBinder[]; ret: WrittenTerm; span: Span }

export interface Data { kind: "data"; name: Name; params: WrittenBinder[]; ctors: Ctor[]; span: Span }

export interface Header { params: Param[]; returns: WrittenBinder[] }

export interface Fn extends Header { kind: "fn"; name: Name; body: Expr & { kind: "block" }; span: Span }

export type Top =
  | Data
  | Fn
  | { kind: "mutual"; decls: Data[] | Fn[]; span: Span }
  | Stmt
  | { kind: "print"; expr: Expr; span: Span }
  | { kind: "goal"; type: WrittenTerm | Header; span: Span }
  | { kind: "qed"; expr: Expr; span: Span };

export interface Program { tops: Top[]; span: Span }
