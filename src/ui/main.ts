import { h, load, save } from "./dom.ts";
import { Workspace } from "./workspace.ts";
import { nat, vec, vheadBy } from "../examples.ts";

const example = `${[nat, vec, vheadBy(""), `let x = VCons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), x);`].join("\n\n")}
`;

const phase = h("select", { "aria-label": "Phase", onchange: () => { save("phase", phase.value); workspace.run(); } },
  h("option", { value: "1" }, "1"), h("option", { value: "2" }, "2"));
phase.value = load("phase") === "2" ? "2" : "1";

const workspace = new Workspace([{ text: example, key: "source" }], () => phase.value === "2" ? 2 : 1);
workspace.mount([h("h1", {}, "Pledge"), h("label", {}, "Phase ", phase),
  h("a", { href: "tutorial.html" }, "Tutorial")], "Restore the example");
