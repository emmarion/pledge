import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "../check.ts";
import { explainTerm, scopeOf } from "../../tests/helpers.ts";
import { page, program, run } from "../../tests/tutorial.ts";

const errorAt = (slug: string, learner: string, at: string, after = "") => {
  const { source, r } = run(slug, learner);
  assert.equal(r.error?.span.start, source.indexOf(at, source.indexOf(after)), r.error?.message());
  return r.error!.message();
};

const keepN = page("erased-positions").solution.replace("erased m is n", "m is n")
  .replace("erased n : Nat(), v", "n : Nat(), v");

test("erased: the start fails at VCons's field A in vcons; the solution prints erased fields as _ and Scope tags A and n", () => {
  assert.match(errorAt("erased", page("erased").initial, "A, n, x, v)", "VCons(A"), /`A` is erased/);
  const { source, r } = run("erased", page("erased").solution);
  assert.deepEqual(r.prints.map(p => p.value), ["Succ(Zero())", "VCons(_, _, Zero(), VCons(_, _, Succ(Zero()), VNil(_)))"]);
  assert.deepEqual(scopeOf(r.infoAt(source.indexOf("vhead(A, n, rest)"))).slice(0, 2), ["A : Type()", "n : Nat()"]);
  assert.deepEqual(r.infoAt(source.indexOf("vhead(A, n, rest)")).scope.slice(0, 2).map(e => e.erased), [true, true]);
});

test("erased-positions: the start fails at n in len's body, and either fix leaves k erased and Succ(Zero())", () => {
  assert.match(errorAt("erased-positions", page("erased-positions").initial, "n\n}"), /`n` is erased/);
  for (const fix of [page("erased-positions").solution, keepN]) {
    const { source, r } = run("erased-positions", fix);
    const k = r.infoAt(source.indexOf("print w")).scope.find(e => e.names.includes("k"));
    assert.deepEqual([k?.erased, k?.rule?.text], [true, "Succ(Zero())"]);
  }
});

test("erased-positions: both fixes check, and only keeping n lets print show the length", () => {
  const p = page("erased-positions");
  const printed = (learner: string) => check(program(p.boxes, `${learner}print len(Nat(), Succ(Zero()), v);\n`), p.phase);
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

test("holes: Expected and the term at a `_` show its parameter and solution", () => {
  const { source, r } = run("holes", page("holes").solution);
  const at = source.indexOf("vhead(_, _, v)") + 6;
  assert.deepEqual(r.infoAt(at).expected.entries?.map(e => [e.name, e.erased]), [["A", true]]);
  assert.deepEqual([explainTerm(r, at)?.canonical.text, explainTerm(r, at + 3)?.canonical.text], ["Nat()", "Succ(Zero())"]);
});

test("holes: each limit is reported at the `_`", () => {
  errorAt("holes", "print VNil(_);\n", "_);");
  errorAt("holes", "let (e : Vec(_, Zero())) = VNil(Nat());\n", "_, Zero()))");
  errorAt("holes", "let w = VCons(Nat(), Zero(), Zero(), VNil(Nat()));\nprint VCons(_, _, _, w);\n", "_, w)");
  const later = `fn vrep(n : Nat()) -> (v : Vec(Nat(), n)) {
  sorry(_)
}
fn num(x : Nat()) -> (n : Nat()) {
  x
}
let i = VCons(_, _, Zero(), vrep(num(Zero())));
`;
  assert.match(errorAt("holes", later, "_, Zero(), vrep"), /only to what exists before it/);
});

test("match-erased: a many match on p, and a second live branch, are rejected; erased r allows it; the branch knows n is m", () => {
  const head = page("match-erased").solution.split("  match")[0]!;
  errorAt("match-erased", `${head}  match p : _ {\n    Refl(_, _) => v;\n  }\n}\n`, "p : _");
  const twoBranches = (r: string) => `fn g(erased n : Nat()) -> (${r} : Nat()) {
  match erased n : (${r} : Nat()) { Zero() => Zero(); Succ(k) => k; }
}
`;
  errorAt("match-erased", twoBranches("r"), "Succ(k) => k;");
  assert.equal(run("match-erased", twoBranches("erased r")).r.error, null);
  const { source, r } = run("match-erased", page("match-erased").solution);
  assert.ok(scopeOf(r.infoAt(source.indexOf("=> v") + 3)).includes("n : Nat() is m"));
  assert.deepEqual(r.prints.map(p => p.value), ["VCons(_, _, Zero(), VNil(_))"]);
});
