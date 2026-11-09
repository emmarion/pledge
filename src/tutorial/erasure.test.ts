import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { page, program } from "../../tests/tutorial.ts";

test("erased-positions: both fixes check, and only keeping n lets print show the length", () => {
  const p = page("erased-positions");
  const printed = (learner: string) => check(program(p.boxes, `${learner}print len(Nat(), Succ(Zero()), v);\n`), p.phase);
  const keepN = p.solution.replace("erased m is n", "m is n").replace("erased n : Nat(), v", "n : Nat(), v");
  assert.equal(check(program(p.boxes, keepN), p.phase).error, null);
  assert.deepEqual(printed(keepN).prints.map(x => x.value).at(-1), "Succ(Zero())");
  assert.match(printed(p.solution).error?.message() ?? "", /erased/);
});

test("holes: a block's final expression takes part in solving a `_`", () => {
  const p = page("holes");
  const r = check(program(p.boxes, `${p.solution}print vhead(_, _, { v });\n`), p.phase);
  assert.equal(r.error && r.error.message(), null);
  assert.equal(r.prints.at(-1)?.value, "Zero()");
});
