import { h, load, save } from "./dom.ts";
import { Workspace } from "./workspace.ts";
import { example } from "../examples.ts";

const phase = h("select", { onchange: () => { save("phase", phase.value); workspace.run(); } },
  h("option", { value: "1" }, "1"), h("option", { value: "2" }, "2 (adds erasure)"));
phase.value = load("phase") === "2" ? "2" : "1";

const workspace = new Workspace([{ text: example, key: "source" }], () => phase.value === "2" ? 2 : 1);
workspace.mount([h("h1", {}, "Pledge"),
  h("label", { title: "The language comes in phases; phase 2 adds erasure." }, "Phase ", phase),
  h("a", { href: "tutorial.html" }, "Tutorial")],
  { label: "Restore the example", question: "Replace your program with the example? This cannot be undone." },
  h("p", { class: "intro" }, "Pledge is a small language for learning dependent types. This page checks the program ",
    "below as you type, and the panels show what the checker knows at the caret. New here? Start with the ",
    h("a", { href: "tutorial.html" }, "tutorial"), "."));
