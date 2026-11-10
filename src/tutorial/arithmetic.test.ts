import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { gapsTest, page, program } from "../../tests/tutorial.ts";

gapsTest([
  ["plus-succ", ["q : Plus(Zero(), Succ(n), Succ(n))", "q : Plus(Succ(m1), Succ(n), Succ(Succ(r1)))"]],
  ["plus-comm", ["q : Plus(n, Zero(), n)", "q : Plus(n, Succ(m1), Succ(r1))"]],
  ["plus-assoc", ["bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(Zero(), bc, r)"]],
  ["times-distrib", ["ab : Nat(), ac : Nat(), t1 : Times(Zero(), b, ab), t2 : Times(Zero(), c, ac), q : Plus(ab, ac, Zero())"]],
]);

test("times-distrib: a binder the later clauses of its `let` refer to needs a type", () => {
  const p = page("times-distrib");
  const r = check(program(p.boxes.map(b => b.replace("let (yxz : Nat(),", "let (yxz,")), p.solution), p.phase);
  assert.match(r.error?.message() ?? "", /`yxz` has no type here/);
});
