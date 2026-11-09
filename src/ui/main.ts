import { h, load, save } from "./dom.ts";
import { Workspace } from "./workspace.ts";

const example = `data Nat() : Type() {
  Zero() : Nat();
  Succ(pred : Nat()) : Nat();
}

data Vec(A : Type(), n : Nat()) : Type() {
  VNil(A : Type()) : Vec(A, Zero());
  VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));
}

fn vhead(A : Type(), n : Nat(), v : Vec(A, Succ(n))) -> (x : A) {
  let VCons(_, _, hd, _) = v;
  hd
}

let x = VCons(Nat(), Zero(), Zero(), VNil(Nat()));
print vhead(Nat(), Zero(), x);
`;

const phase = h("select", { "aria-label": "Phase", onchange: () => { save("phase", phase.value); workspace.run(); } },
  h("option", { value: "1" }, "1"), h("option", { value: "2" }, "2"));
phase.value = load("phase") === "2" ? "2" : "1";

const workspace = new Workspace([{ text: example, key: "source" }], () => phase.value === "2" ? 2 : 1);
workspace.mount([h("h1", {}, "Pledge"), h("label", {}, "Phase ", phase), h("a", { href: "tutorial.html" }, "Tutorial")], "Restore the example");
