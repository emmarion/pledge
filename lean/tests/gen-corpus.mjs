import { cpSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { verdict } from "./verdict.mjs";

const root = fileURLToPath(new URL("../../", import.meta.url));
const out = process.argv[2] ?? fileURLToPath(new URL("corpus.json", import.meta.url));
const { pages } = await import(join(root, "src/tutorial/pages.ts"));

const recordCalls = () => {
  const scratch = mkdtempSync(join(tmpdir(), "pledge-corpus-"));
  try {
    const skip = new Set([".git", "node_modules", "lean", "dist", ".claude"]);
    cpSync(root, scratch, { recursive: true, filter: src => !skip.has(src.slice(root.length).split("/")[0]) });
    const checkTs = join(scratch, "src/check.ts"), log = join(scratch, "calls.jsonl");
    const text = readFileSync(checkTs, "utf8");
    const patched = text.replace("export const check: Check =", "const check0: Check =");
    if (patched === text) throw new Error("src/check.ts no longer has the line the patch replaces");
    writeFileSync(checkTs, `import { appendFileSync } from "node:fs";\n${patched}
export const check: Check = (source, phase, where) => {
  const frame = new Error().stack!.split("\\n").find(l => /\\.test\\.ts:\\d+/.test(l)) ?? "";
  const origin = /([\\w-]+(?:\\/[\\w-]+)*\\.test\\.ts):(\\d+)/.exec(frame.slice(frame.indexOf("src/")));
  appendFileSync(process.env.PLEDGE_CALLS!, JSON.stringify({ source, phase,
    origin: origin ? \`\${origin[1]}:\${origin[2]}\` : "test" }) + "\\n");
  return check0(source, phase, where);
};\n`);
    writeFileSync(log, "");
    const run = spawnSync(process.execPath, ["--test", "src/**/*.test.ts"],
      { cwd: scratch, env: { ...process.env, PLEDGE_CALLS: log }, encoding: "utf8" });
    if (run.status !== 0) throw new Error(`the test suite failed:\n${run.stdout}\n${run.stderr}`);
    const byLine = (a, b) =>
      a.origin.localeCompare(b.origin, "en", { numeric: true }) || (a.source < b.source ? -1 : 1);
    return readFileSync(log, "utf8").split("\n").filter(Boolean).map(l => JSON.parse(l)).sort(byLine);
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
};

const pledgeFiles = ["tests", "lean/tests/extra"].flatMap(dir => readdirSync(join(root, dir))
  .filter(f => f.endsWith(".pledge")).sort().map(f => ({ source: readFileSync(join(root, dir, f), "utf8"),
    phase: f.startsWith("phase2_") ? 2 : 1, origin: `${dir}/${f}` })));
const tutorial = pages.flatMap(p => [["initial", p.initial], ["solution", p.solution]].map(([which, learner]) =>
  ({ source: [...p.boxes, learner].join("\n"), phase: p.phase, origin: `tutorial/${p.slug}/${which}` })));

const seen = new Set();
const programs = [...pledgeFiles, ...tutorial, ...recordCalls()].filter(({ source, phase }) => {
  const key = `${phase}\0${source}`;
  return !seen.has(key) && seen.add(key);
}).map((p, i) => ({ id: i, origin: p.origin, phase: p.phase, source: p.source, expected: verdict(p.source, p.phase) }));
writeFileSync(out, `${JSON.stringify({ programs }, null, 1)}\n`);
console.log(`${programs.length} programs written to ${out}`);
