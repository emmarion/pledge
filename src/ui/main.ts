/// <reference types="vite/client" />
import { h, load, save } from "./dom.ts";
import { Workspace } from "./workspace.ts";
import { example, titleOf } from "../examples.ts";
import { repository } from "./links.ts";

const setPhase = (value: string): void => { phase.value = value; save("phase", value); };
const phase = h("select", { onchange: () => { setPhase(phase.value); workspace.run(); } },
  h("option", { value: "1" }, "1"), h("option", { value: "2" }, "2 (adds erasure)"));
phase.value = load("phase") === "2" ? "2" : "1";

const files = import.meta.glob<string>("../../examples/*.pledge", { query: "?raw", import: "default", eager: true });
const programs = [{ title: "Nat, Vec and vhead", text: example, phase: null },
  ...Object.entries(files).map(([file, text]) => ({ title: titleOf(file, text), text, phase: "2" }))];
const picker = h("select", { id: "example" }, programs.map((p, i) => h("option", { value: String(i) }, p.title)));
const open = (): void => {
  const program = programs[Number(picker.value)]!;
  if (!workspace.replace("Replace your program with this example? This cannot be undone.", () => program.text,
    () => programs.map(p => p.text))) return;
  if (program.phase) setPhase(program.phase);
  workspace.run();
};

const workspace = new Workspace([{ text: example, key: "source" }], () => phase.value === "2" ? 2 : 1);
workspace.mount([h("h1", {}, "Pledge"),
  h("label", { title: "The language comes in phases; phase 2 adds erasure." }, "Phase ", phase),
  h("a", { href: "tutorial.html" }, "Tutorial"), h("a", { href: repository }, "GitHub")],
  [h("label", { for: "example" }, "Example"), picker, h("button", { type: "button", onclick: open }, "Open")],
  h("p", { class: "intro" }, "Pledge is a small language for learning restricted dependent types. This page checks ",
    "the program below as you type, and the panels show what the checker knows at the caret. New here? Start with the ",
    h("a", { href: "tutorial.html" }, "tutorial"), "."));
