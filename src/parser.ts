import type { Ann, Arg, WrittenBinder, Branch, Ctor, Data, Expr, Fn, Header, Id, LetBinder, Mult, Param, Pattern,
  Phase, Program, Span, Stmt, Tele, WrittenTerm, Top, TypedParam } from "./syntax.ts";
import type { Diagnostic } from "./api.ts";
import { lex, type Token } from "./lexer.ts";
import { attempt, fail } from "./context.ts";

type Block = Expr & { kind: "block" };

const tokenText = (token: Token): string =>
  token.kind === "eof" ? "end of input" : token.kind === "keyword" ? `keyword \`${token.text}\`` : `\`${token.text}\``;

interface Grammar { program(): Program; expression(): Expr }

export function parse(source: string, phase: Phase): { program: Program } | { error: Diagnostic } {
  const r = parseWith(source, phase, g => g.program());
  return "error" in r ? r : { program: r.value };
}

export function parseExpr(source: string, phase: Phase): { expr: Expr } | { error: Diagnostic } {
  const r = parseWith(source, phase, g => g.expression());
  return "error" in r ? r : { expr: r.value };
}

function parseWith<T>(source: string, phase: Phase, root: (g: Grammar) => T): { value: T } | { error: Diagnostic } {
  const tokens = lex(source, phase);
  let pos = 0;
  let prevEnd = 0;

  const peek = (k = 0): Token => {
    const token = tokens[Math.min(pos + k, tokens.length - 1)]!;
    if (token.kind === "error") fail(token.diag.span, token.diag.message);
    return token;
  };
  const next = (): Token => {
    const token = peek();
    pos++;
    prevEnd = token.span.end;
    return token;
  };
  const syntaxError = (expected: string): never => {
    const token = peek();
    return fail(token.span, () => `expected ${expected}, found ${tokenText(token)}`);
  };
  const isText = (token: Token, text: string): boolean => token.kind !== "name" && token.text === text;
  const at = (text: string): boolean => isText(peek(), text);
  const eat = (text: string): boolean => at(text) && (next(), true);
  const expect = (text: string): Token => (at(text) ? next() : syntaxError(`\`${text}\``));
  const start = (): number => peek().span.start;
  const spanFrom = (begin: number): Span => ({ start: begin, end: prevEnd });
  const skipExtraSemis = (): void => { while (eat(";")); };
  const declaration = <T>(result: T): T => (skipExtraSemis(), result);
  const braces = <T>(item: () => T): T[] => {
    expect("{");
    const items: T[] = [];
    while (!at("}")) items.push(item());
    expect("}");
    return items;
  };
  const endStatement = (begin: number): Span => {
    expect(";");
    const span = spanFrom(begin);
    skipExtraSemis();
    return span;
  };

  const commaList = <T>(item: () => T, close: string, minOne: boolean): T[] => {
    const items: T[] = [];
    if (minOne || !at(close)) do items.push(item()); while (eat(","));
    return items;
  };
  const parens = <T>(item: () => T, minOne: boolean): T[] => {
    expect("(");
    const items = commaList(item, ")", minOne);
    expect(")");
    return items;
  };

  const name = (): Id => {
    const token = peek();
    return token.kind === "name" ? (next(), { name: token.text, span: token.span }) : syntaxError("a name");
  };
  const id = (): Id => (peek().kind === "underscore" ? { name: null, span: next().span } : peek().kind === "name"
    ? name() : syntaxError("a name or `_`"));
  const isMult = (token: Token): boolean => token.kind === "keyword"
    && (token.text === "erased" || token.text === "many");
  const mult = (): Mult | null => (isMult(peek()) ? (next().text as Mult) : null);

  const term = (): WrittenTerm => {
    const begin = start();
    const head = name();
    const args = at("(") ? parens(term, false) : null;
    return { head, args, span: spanFrom(begin) };
  };
  const annOpt = (): Ann | null =>
    eat(":") ? { kind: "type", term: term() } : eat("is") ? { kind: "is", term: term() } : null;

  const letBinderWith = (multAllowed: boolean) => (): LetBinder => {
    const begin = start();
    const m = multAllowed ? mult() : null;
    const binderName = id();
    return { name: binderName, ann: annOpt(), mult: m, span: spanFrom(begin) };
  };
  const letBinder = letBinderWith(true);
  const binderWith = (multAllowed: boolean) => (): WrittenBinder => {
    const b = letBinderWith(multAllowed)();
    return b.ann ? { ...b, ann: b.ann } : syntaxError("`:` or `is`");
  };
  const binder = binderWith(true);
  const tele = (): WrittenBinder[] => parens(binder, true);
  const isUnderscoreTele = (): boolean => peek().kind === "underscore" && !isText(peek(1), ":")
    && !isText(peek(1), "is");

  const param = (): Param => {
    const begin = start();
    const subterm = eat("subterm");
    return { ...binder(), subterm, span: spanFrom(begin) };
  };
  const pattern = (): Pattern => {
    const begin = start();
    const ctor = name();
    return { ctor, fields: parens(id, false), span: spanFrom(begin) };
  };

  const arg = (): Arg => {
    const begin = start();
    const mark = at("subterm") || at("same") ? (next().text as "subterm" | "same") : null;
    const value: Expr = phase >= 2 && peek().kind === "underscore"
      ? { kind: "var", name: { name: null, span: peek().span }, span: next().span }
      : expr();
    return { mark, expr: value, span: spanFrom(begin) };
  };

  const expr = (): Expr => {
    const begin = start();
    const token = peek();
    if (token.kind === "name") {
      const head = name();
      return at("(") ? { kind: "app", head, args: parens(arg, false), span: spanFrom(begin) }
        : { kind: "var", name: head, span: head.span };
    }
    if (at("(")) return { kind: "tuple", elems: parens(expr, true), span: spanFrom(begin) };
    if (at("{")) return block();
    if (eat("match")) {
      const m = mult();
      const scrut = expr();
      expect(":");
      const ann: Tele = peek().kind === "underscore" ? (next(), "_") : tele();
      const branches = braces((): Branch => {
        const branchBegin = start();
        const pat = pattern();
        expect("=>");
        const body = expr();
        return { pat, body, span: endStatement(branchBegin) };
      });
      return { kind: "match", mult: m, scrut, ann, branches, span: spanFrom(begin) };
    }
    if (eat("sorry")) {
      expect("(");
      const sorryTele: Tele = isUnderscoreTele() ? (next(), "_") : commaList(binderWith(false), ")", true);
      expect(")");
      return { kind: "sorry", tele: sorryTele, span: spanFrom(begin) };
    }
    return syntaxError("an expression");
  };

  const block = (): Block => {
    const begin = start();
    expect("{");
    const stmts: Stmt[] = [];
    while (at("let") || at("inspect")) stmts.push(stmt());
    const final = expr();
    if (isText(tokens[pos - 1]!, "}")) skipExtraSemis();
    expect("}");
    return { kind: "block", stmts, final, span: spanFrom(begin) };
  };

  const patLet = (begin: number, comptime: boolean): Stmt => {
    const m = mult();
    const pat = pattern();
    expect("=");
    const rhs = expr();
    return { kind: "patlet", comptime, mult: m, pat, rhs, span: endStatement(begin) };
  };

  const stmt = (): Stmt => {
    const begin = start();
    if (eat("inspect")) return { kind: "inspect", span: endStatement(begin) };
    expect("let");
    const k = isMult(peek()) ? 1 : 0;
    if (peek(k).kind === "name" && isText(peek(k + 1), "(")) return patLet(begin, false);
    const binders = k === 0 && at("(") ? parens(letBinder, true) : [letBinder()];
    expect("=");
    const rhs = expr();
    return { kind: "let", binders, rhs, span: endStatement(begin) };
  };

  const data = (): Data => {
    const begin = start();
    expect("data");
    const dataName = name();
    const params = parens((): TypedParam => {
      const paramBegin = start();
      const paramName = id();
      expect(":");
      return { name: paramName, type: term(), span: spanFrom(paramBegin) };
    }, false);
    expect(":");
    if (peek().kind === "name" && peek().text === "Type") next();
    else syntaxError("`Type`");
    expect("(");
    expect(")");
    const ctors = braces((): Ctor => {
      const ctorBegin = start();
      const ctorName = name();
      const fields = parens(binder, false);
      expect(":");
      const ret = term();
      return { name: ctorName, fields, ret, span: endStatement(ctorBegin) };
    });
    return declaration({ kind: "data", name: dataName, params, ctors, span: spanFrom(begin) });
  };

  const header = (): Header => {
    const params = parens(param, false);
    expect("->");
    return { params, returns: tele() };
  };

  const fn = (): Fn => {
    const begin = start();
    expect("fn");
    const fnName = name();
    const h = header();
    const body = block();
    return declaration({ kind: "fn", name: fnName, ...h, body, span: spanFrom(begin) });
  };

  const mutual = (): Top => {
    const begin = start();
    expect("mutual");
    const datas: Data[] = [];
    const fns: Fn[] = [];
    braces((): void => {
      if (at("data") && fns.length === 0) datas.push(data());
      else if (at("fn") && datas.length === 0) fns.push(fn());
      else if (at("data") || at("fn")) fail(peek().span, () =>
        "a `mutual` block holds either `data` declarations or functions, not both");
      else syntaxError("`data` or `fn`");
    });
    if (datas.length === 0 && fns.length === 0) fail(tokens[pos - 1]!.span, () =>
      "a `mutual` block declares at least one `data` declaration or function");
    return declaration({ kind: "mutual", decls: datas.length > 0 ? datas : fns, span: spanFrom(begin) });
  };

  const top = (): Top => {
    const begin = start();
    if (at("data")) return data();
    if (at("fn")) return fn();
    if (at("mutual")) return mutual();
    if (at("let") || at("inspect")) return stmt();
    if (eat("comptime")) {
      expect("let");
      return patLet(begin, true);
    }
    if (eat("print")) return { kind: "print", expr: expr(), span: endStatement(begin) };
    if (eat("goal")) return { kind: "goal", type: eat("fn") ? header() : term(), span: endStatement(begin) };
    if (eat("qed")) return { kind: "qed", expr: expr(), span: endStatement(begin) };
    return syntaxError("a declaration or a top-level statement");
  };

  const program = (): Program => {
    const tops: Top[] = [];
    while (peek().kind !== "eof") tops.push(top());
    return { tops, span: { start: 0, end: source.length } };
  };
  const expression = (): Expr => {
    const e = expr();
    return peek().kind === "eof" ? e : syntaxError("end of input");
  };

  return attempt(() => ({ value: root({ program, expression }) }));
}
