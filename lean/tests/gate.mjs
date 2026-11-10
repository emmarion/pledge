import { mkdtempSync, readFileSync, readdirSync, rmSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const lean = fileURLToPath(new URL("../", import.meta.url));
const allowedAxioms = ["propext", "Classical.choice", "Quot.sound"];
const forbidden = /\b(axiom|partial|unsafe|implemented_by|extern|opaque|native_decide|sorryAx|admit|skipKernelTC)\b/;
const tacticSorry = /(^|[^.«\w])sorry\b/;
const fuel = /fuel/i;

const run = (cmd, args) => {
  const r = spawnSync(cmd, args, { cwd: lean, encoding: "utf8", maxBuffer: 1 << 28 });
  return { ok: r.status === 0, out: (r.stdout ?? "") + (r.stderr ?? "") + (r.error ? String(r.error) : "") };
};
const fail = (what, detail = "") => {
  console.log(`gate: FAIL: ${what}${detail && "\n" + detail}`);
  process.exit(1);
};
const pass = what => console.log(`gate: ok: ${what}`);

function code(src) {
  let i = 0;
  const scan = inner => {
    let out = "", depth = 0;
    while (i < src.length) {
      const c = src[i], two = src.slice(i, i + 2);
      if (two === "/-") {
        let d = 0;
        do {
          if (src.startsWith("/-", i)) { d++; i += 2; } else if (src.startsWith("-/", i)) { d--; i += 2; } else i++;
        } while (d > 0 && i < src.length);
        out += " ";
      } else if (two === "--") {
        while (i < src.length && src[i] !== "\n") i++;
      } else if (c === '"') {
        const interpolated = /[smf]!$/.test(src.slice(0, i));
        i++;
        while (i < src.length && src[i] !== '"') {
          if (src[i] === "\\") i += 2;
          else if (interpolated && src[i] === "{") { i++; out += " " + scan(true) + " "; i++; }
          else i++;
        }
        i++;
        out += '""';
      } else if (c === "'" && !/[\p{L}\p{N}_'!?]/u.test(src[i - 1] ?? " ")) {
        i += src[i + 1] === "\\" ? 4 : 3;
        out += "' '";
      } else if (inner && c === "}" && depth === 0) {
        return out;
      } else {
        if (inner && c === "{") depth++;
        if (inner && c === "}") depth--;
        out += c;
        i++;
      }
    }
    return out;
  };
  return scan(false);
}

const build = run("lake", ["build"]);
if (!build.ok) fail("lake build", build.out.split("\n").slice(-30).join("\n"));
const bad = build.out.split("\n").filter(l => /declaration uses .sorry.|error:/.test(l));
if (bad.length) fail("build output", bad.join("\n"));
pass("lake build, no sorry");

const sources = ["Main.lean", "Pledge.lean", ...readdirSync(join(lean, "Pledge"), { recursive: true })
  .filter(f => f.endsWith(".lean")).map(f => join("Pledge", f))];
const partialOk = ["evalExpr", "evalList", "evalCall", "evalBlock", "evalStmt"]
  .map(n => `${join("Pledge", "Eval.lean")}: partial def ${n} `);
const lines = sources.flatMap(f => code(readFileSync(join(lean, f), "utf8")).split("\n").map(l => `${f}: ${l.trim()}`));
const partials = lines.filter(l => partialOk.some(p => l.startsWith(p)));
if (partials.length !== partialOk.length) fail("the allowed partial evaluator", partials.join("\n"));
const hits = lines.map(l => partials.includes(l) ? l.replace(": partial def ", ": def ") : l)
  .filter(l => forbidden.test(l) || tacticSorry.test(l) || fuel.test(l));
if (hits.length) fail("forbidden constructs in the sources", hits.join("\n"));
pass(`${sources.length} source files free of axiom, unsafe, opaque, sorry, fuel and the like, and of partial ` +
  `outside the ${partialOk.length} declarations of the evaluator allowed it`);

const audit = run("lake", ["env", "lean", "tests/Audit.lean"]);
if (!audit.ok) fail("tests/Audit.lean", audit.out);
const names = [...readFileSync(join(lean, "tests/Audit.lean"), "utf8").matchAll(/#print axioms (\S+)/g)].map(m => m[1]);
for (const n of names) {
  const line = audit.out.split("\n").find(l => l.startsWith(`'Pledge.${n}'`));
  const listed = line?.match(/depends on axioms: \[(.*)\]/)?.[1].split(", ");
  const axioms = listed ?? (line?.includes("does not depend") ? [] : null);
  if (!axioms || axioms.some(a => !allowedAxioms.includes(a))) fail(`axioms of ${n}`, line ?? audit.out);
}
pass(`${names.length} headline theorems use only ${allowedAxioms.join(", ")}`);

const dir = mkdtempSync(join(tmpdir(), "pledge-gate-"));
const corpus = join(dir, "corpus.json");
const gen = run("node", ["tests/gen-corpus.mjs", corpus]);
const fresh = gen.ok && readFileSync(corpus, "utf8") === readFileSync(join(lean, "tests/corpus.json"), "utf8");
rmSync(dir, { recursive: true, force: true });
if (!fresh) fail("tests/corpus.json is not what tests/gen-corpus.mjs writes from src/", gen.ok ? "" : gen.out);
pass("tests/corpus.json is current");

const compare = run("node", ["tests/compare.mjs"]);
const summary = compare.out.trim().split("\n").at(-1);
if (!compare.ok || !/ 0 disagree/.test(summary)) fail("differential comparison", compare.out.slice(-3000));
pass(summary);
