import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { parseArgs } from "node:util";

const here = fileURLToPath(new URL(".", import.meta.url));
const { values: opt } = parseArgs({ options: {
  exe: { type: "string", default: process.env.PLEDGE_EXE ?? join(here, "../.lake/build/bin/pledge") },
  corpus: { type: "string", default: join(here, "corpus.json") },
  filter: { type: "string" },
  "phase1-only": { type: "boolean", default: false },
  verbose: { type: "boolean", default: false },
} });

const { programs } = JSON.parse(readFileSync(opt.corpus, "utf8"));
const chosen = programs.filter(p => !(opt["phase1-only"] && p.phase === 2) &&
  (!opt.filter || p.origin.includes(opt.filter) || p.source.includes(opt.filter)));
const dir = mkdtempSync(join(tmpdir(), "pledge-compare-"));
const show = v => JSON.stringify(v);
const values = v => show(v.prints?.map(p => p.value));
const required = [
  ["error", v => show(v.error === null)],
  ["prints", values],
  ...["qed", "goalProved", "containsSorry"].map(k => [k, v => show(v[k])]),
];
const informational = [
  ["error pos", v => show(v.error?.pos)],
  ["error message", v => show(v.error?.message)],
  ["print positions", v => show(v.prints?.map(p => p.pos))],
  ["inspect positions", v => show(v.inspects?.map(p => p.pos))],
];
const differ = (checks, a, b) => checks.filter(([, f]) => f(a) !== f(b)).map(([k]) => k);

let failed = 0, infoOnly = 0;
for (const p of chosen) {
  const file = join(dir, `${p.id}.pledge`);
  writeFileSync(file, p.source);
  const run = spawnSync(opt.exe, ["check", "--phase", String(p.phase), file], { encoding: "utf8" });
  let actual = null;
  try { actual = JSON.parse(run.stdout); } catch {}
  const bad = actual ? differ(required, p.expected, actual) : [`no JSON from the executable (status ${run.status})`];
  const notes = actual ? differ(informational, p.expected, actual) : [];
  if (bad.length) {
    failed++;
    const brief = v => show({ ...v, inspects: undefined });
    console.log(`FAIL #${p.id} ${p.origin} phase ${p.phase}: ${bad.join(", ")}\n  file: ${file}` +
      `\n  typescript: ${brief(p.expected)}` +
      `\n  lean:       ${actual ? brief(actual) : String(run.error ?? run.stdout + run.stderr).trim()}`);
    continue;
  }
  rmSync(file);
  if (notes.length) infoOnly++;
  if (notes.length && opt.verbose) console.log(`info #${p.id} ${p.origin}: ${notes.join(", ")}` +
    `\n  typescript: ${show(p.expected.error)}\n  lean:       ${show(actual.error)}`);
}
if (!failed) rmSync(dir, { recursive: true, force: true });
console.log(`${chosen.length} programs (${programs.length - chosen.length} skipped): ` +
  `${chosen.length - failed} agree, ${failed} disagree, ${infoOnly} agree with informational differences` +
  (failed ? `; sources kept in ${dir}` : ""));
process.exitCode = failed ? 1 : 0;
