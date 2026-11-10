import type { Section } from "./pages.ts";
import { nat } from "../examples.ts";
import { paragraphs, box, plusRel, gap, withQed } from "./programs.ts";

const times = `data Times(m : Nat(), n : Nat(), r : Nat()) : Type() {
  TimesZero(n : Nat()) : Times(Zero(), n, Zero());
  TimesSucc(m : Nat(), n : Nat(), r : Nat(), s : Nat(),
      t : Times(m, n, r), p : Plus(r, n, s)) : Times(Succ(m), n, s);
}`;

const plusZeroRight = `fn plusZeroRight(subterm n : Nat()) -> (p : Plus(n, Zero(), n)) {
  match n : _ {
    Zero() => PlusZero(Zero());
    Succ(k) => PlusSucc(k, Zero(), k, plusZeroRight(subterm k));
  }
}`;

const lemma = (name: string, conclusion: string) => ({
  fn: (zero: string, succ: string): string => `fn ${name}(m : Nat(), n : Nat(), r : Nat(), subterm p : Plus(m, n, r))
    -> (q : ${conclusion}) {
  match p : _ {
    PlusZero(_) =>${zero};
    PlusSucc(m1, _, r1, p1) =>${succ};
  }
}`,
  goal: `goal fn (m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r))
    -> (q : ${conclusion});`,
});

const plusSuccLemma = lemma("plusSucc", "Plus(m, Succ(n), Succ(r))");

const plusSucc = plusSuccLemma.fn(" PlusZero(Succ(n))", `
      PlusSucc(m1, Succ(n), Succ(r1), plusSucc(m1, n, r1, subterm p1))`);

const plusCommLemma = lemma("plusComm", "Plus(n, m, r)");

const plusComm = plusCommLemma.fn(" plusZeroRight(n)", `
      plusSucc(n, m1, r1, plusComm(m1, n, r1, subterm p1))`);

const plusAssocWith = (zero: string): string => `fn plusAssoc(a : Nat(), b : Nat(), c : Nat(), ab : Nat(), r : Nat(),
    subterm p : Plus(a, b, ab), q : Plus(ab, c, r))
    -> (bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(a, bc, r)) {
  match p : _ {
    PlusZero(_) =>${zero};
    PlusSucc(a1, _, ab1, p1) => {
      let PlusSucc(_, _, r1, q3) = q;
      let (bc, s1, s2) = plusAssoc(a1, b, c, ab1, r1, subterm p1, q3);
      (bc, s1, PlusSucc(a1, bc, r1, s2))
    };
  }
}`;

const plusAssoc = plusAssocWith(" (r, q, PlusZero(r))");

const plusAssocRev = `fn plusAssocRev(a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), subterm q : Plus(a, bc, r))
    -> (ab : Nat(), q1 : Plus(a, b, ab), q2 : Plus(ab, c, r)) {
  match q : _ {
    PlusZero(_) => (b, PlusZero(b), p);
    PlusSucc(a1, _, r1, q3) => {
      let (ab1, s1, s2) = plusAssocRev(a1, b, c, bc, r1, p, subterm q3);
      (Succ(ab1), PlusSucc(a1, b, ab1, s1), PlusSucc(ab1, c, r1, s2))
    };
  }
}`;

const exchange = `fn exchange(w : Nat(), y : Nat(), x : Nat(), z : Nat(), wy : Nat(),
    xz : Nat(), r : Nat(), p : Plus(w, y, wy), q : Plus(x, z, xz),
    s : Plus(wy, xz, r))
    -> (wx : Nat(), yz : Nat(), p1 : Plus(w, x, wx),
        q1 : Plus(y, z, yz), s1 : Plus(wx, yz, r)) {
  let (yxz : Nat(), s2 : Plus(y, xz, yxz), s3 : Plus(w, yxz, r)) =
    plusAssoc(w, y, xz, wy, r, p, s);
  let (yx : Nat(), s4 : Plus(y, x, yx), s5 : Plus(yx, z, yxz)) =
    plusAssocRev(y, x, z, xz, yxz, q, s2);
  let (s6 : Plus(x, y, yx)) = plusComm(y, x, yx, s4);
  let (yz : Nat(), s7 : Plus(y, z, yz), s8 : Plus(x, yz, yxz)) =
    plusAssoc(x, y, z, yx, yxz, s6, s5);
  let (wx : Nat(), s9 : Plus(w, x, wx), s10 : Plus(wx, yz, r)) =
    plusAssocRev(w, x, yz, yxz, r, s8, s3);
  (wx, yz, s9, s7, s10)
}`;

const timesDistrib = (zero: string): string => `fn timesDistrib(a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), subterm t : Times(a, bc, r))
    -> (ab : Nat(), ac : Nat(), t1 : Times(a, b, ab),
        t2 : Times(a, c, ac), q : Plus(ab, ac, r)) {
  match t : _ {
    TimesZero(_) =>${zero};
    TimesSucc(a1, _, r1, _, t3, p1) => {
      let (ab1, ac1, t4, t5, q1) =
        timesDistrib(a1, b, c, bc, r1, p, subterm t3);
      let (ab, ac, s1, s2, q2) =
        exchange(ab1, ac1, b, c, r1, bc, r, q1, p, p1);
      (ab, ac, TimesSucc(a1, b, ab1, ab, t4, s1),
        TimesSucc(a1, c, ac1, ac, t5, s2), q2)
    };
  }
}`;

const plusAssocGoal = `goal fn (a : Nat(), b : Nat(), c : Nat(), ab : Nat(), r : Nat(),
    p : Plus(a, b, ab), q : Plus(ab, c, r))
    -> (bc : Nat(), q1 : Plus(b, c, bc), q2 : Plus(a, bc, r));`;

const timesDistribGoal = `goal fn (a : Nat(), b : Nat(), c : Nat(), bc : Nat(), r : Nat(),
    p : Plus(b, c, bc), t : Times(a, bc, r))
    -> (ab : Nat(), ac : Nat(), t1 : Times(a, b, ab),
        t2 : Times(a, c, ac), q : Plus(ab, ac, r));`;

const replaceAll = "Replace each `sorry(_)` in your box, until the status line reads \"No sorry\" and \"Goal proved\".";

export const arithmetic: Section = { title: "Arithmetic", optional: true, pages: [
  {
    slug: "plus-succ",
    title: "A lemma about Plus",
    phase: 1,
    prose: paragraphs(
      "This section is optional. Its four pages prove facts about arithmetic that you know from school, each building on the ones before, and nothing after the section depends on it. To skip it, go on to the page \"Proof by reflection\". Writing a + b = c for `Plus(a, b, c)`, this page proves: if m + n = r, then m + (n + 1) = r + 1, where n + 1 is `Succ(n)`. It is a lemma, a small fact proved to help with a bigger one: the next page needs it for commutativity.",
      "Each fact is a function goal, as on the page \"Proof by recursion\": the parameters are the assumptions, and the returns are the conclusion. As on the previous page, `qed plusSucc;` is already in your box, so the status line reads \"qed checks\" and \"Goal not proved\" from the start.",
      "The proof is an induction on m, written as a recursion on the evidence `p`, which is marked `subterm`. The match on `p` has one branch for each way m + n = r can have been shown.",
      "Put the caret on the first `sorry(_)`. Scope shows that `m` is `Zero()` and `r` is `n`, so Expected asks for `Plus(Zero(), Succ(n), Succ(n))`: zero plus `Succ(n)` is `Succ(n)`. One `PlusZero` shows that.",
      "On the second, `m` is `Succ(m1)`, `r` is `Succ(r1)` and `p1 : Plus(m1, n, r1)`, and Expected asks for `Plus(Succ(m1), Succ(n), Succ(Succ(r1)))`. Scope also shows that `p` is `PlusSucc(m1, n, r1, p1)`, so `p1` is a strict subterm of `p`, and the recursive call `plusSucc(m1, n, r1, subterm p1)` is allowed. It gives `Plus(m1, Succ(n), Succ(r1))`, and one `PlusSucc` around it gives what Expected asks for.",
      "The first box also holds `plusZeroRight`, evidence that n + 0 = n, built by recursion on `n`. It is the fact of the page \"Proof by recursion\" in another form: it produces evidence of `Plus` instead of taking it apart. This page does not need it; the next one does."),
    task: replaceAll,
    refs: "§7, §9, §12, §13",
    boxes: [box(nat, plusRel, plusZeroRight), plusSuccLemma.goal],
    initial: `-- Replace each sorry(_).
${withQed(plusSuccLemma.fn(gap, gap), "plusSucc")}`,
    requireQed: true,
    solution: withQed(plusSucc, "plusSucc"),
  },
  {
    slug: "plus-comm",
    title: "Commutativity of addition",
    phase: 1,
    prose: paragraphs(
      "This page proves that the order of a sum does not matter: if m + n = r, then n + m = r. That looks too obvious to need a proof, but `Plus` is defined by cases on its first argument, so its value constructors say nothing directly about the second. Swapping the two takes an induction, and the two lemmas in the second box do the steps.",
      "As on the previous page, the proof is a recursion on `p`, and the `qed` is already in your box.",
      "Put the caret on the first `sorry(_)`. Scope shows that `m` is `Zero()` and `r` is `n`, so Expected asks for `Plus(n, Zero(), n)`: n + 0 = n. No value constructor of `Plus` builds that for an `n` the checker knows nothing about, since both are about the first argument. `plusZeroRight(n)` does, by its own induction on `n`.",
      "On the second, `m` is `Succ(m1)`, `r` is `Succ(r1)` and `p1 : Plus(m1, n, r1)`, and Expected asks for `Plus(n, Succ(m1), Succ(r1))`. The recursive call `plusComm(m1, n, r1, subterm p1)` gives `Plus(n, m1, r1)`: n + m1 = r1. From that, `plusSucc` from the previous page gives n + (m1 + 1) = r1 + 1, which is what Expected asks for. Hover over `plusSucc` to see its parameters and returns.",
      "A call can be an argument of another call, so the whole branch can be a single expression, with the recursive call as the last argument of `plusSucc`."),
    task: replaceAll,
    refs: "§7, §8, §9, §12, §13",
    boxes: [box(nat, plusRel), box(plusZeroRight, plusSucc), plusCommLemma.goal],
    initial: `-- Replace each sorry(_).
${withQed(plusCommLemma.fn(gap, gap), "plusComm")}`,
    requireQed: true,
    solution: withQed(plusComm, "plusComm"),
  },
  {
    slug: "plus-assoc",
    title: "Associativity of addition",
    phase: 1,
    prose: paragraphs(
      "Associativity says that (a + b) + c and a + (b + c) are the same number. With `Plus`, every sum has to be named. Given ab with a + b = ab, and r with ab + c = r, the goal asks for a number bc with b + c = bc and a + bc = r. As with `r` on the page \"Appending vectors\", `bc` can be read as \"there is a `bc` such that\".",
      "Your box holds the whole proof, `qed` included, except for one branch. It is an induction on a, as a recursion on `p`. Read the `PlusSucc(a1, _, ab1, p1)` branch first, from the top.",
      "Put the caret on its first line, the pattern `let` on `q`. Scope shows what forcing `PlusSucc` told the checker: `a` is `Succ(a1)`, `ab` is `Succ(ab1)`, and so `q : Plus(Succ(ab1), c, r)`. A `PlusZero` would need `q`'s first argument to be `Zero()`, so it is refuted, as Refutations shows, and the pattern `let` is accepted. After it, `r` is `Succ(r1)` and `q3 : Plus(ab1, c, r1)`.",
      "The recursive call marks `p1` `subterm`, a strict subterm of `p`. It gives `bc`, `s1 : Plus(b, c, bc)` and `s2 : Plus(a1, bc, r1)`. On the last line, Expected asks for `Plus(Succ(a1), bc, Succ(r1))` as the third result, and `PlusSucc` turns `s2` into that. For now Scope marks `bc`, `s1` and `s2` as tainted: the call relies on the `sorry` still in `plusAssoc`.",
      "Now the `PlusZero` branch. On its `sorry(_)`, Scope shows that `a` is `Zero()` and `ab` is `b`, so `q : Plus(b, c, r)`. Expected asks for a `bc`, evidence of `Plus(b, c, bc)`, and evidence of `Plus(Zero(), bc, r)`. Choosing `bc` is up to you."),
    task: "Replace the `sorry(_)` in the `PlusZero` branch, until the status line reads \"No sorry\" and \"Goal proved\".",
    refs: "§7, §8, §9, §10, §12, §13",
    boxes: [box(nat, plusRel), plusAssocGoal],
    initial: `-- Replace the sorry(_) in the PlusZero branch.
${withQed(plusAssocWith(gap), "plusAssoc")}`,
    requireQed: true,
    solution: withQed(plusAssoc, "plusAssoc"),
  },
  {
    slug: "times-distrib",
    title: "Distributivity of multiplication",
    phase: 1,
    prose: paragraphs(
      "The last proof of this section puts the others to work. `Times(m, n, r)` is the claim that m × n = r. Like `Plus`, it is defined by cases on its first argument: 0 × n = 0, and if m × n = r and r + n = s, then (m + 1) × n = s.",
      "The goal is distributivity: a × (b + c) = a × b + a × c. With every number named, from `Plus(b, c, bc)` and `Times(a, bc, r)` it asks for `ab` and `ac` with `Times(a, b, ab)`, `Times(a, c, ac)` and `Plus(ab, ac, r)`.",
      "Your box holds the proof, an induction on a as a recursion on `t`, except for the `TimesZero` branch. Put the caret on its `sorry(_)`: Scope shows that `a` and `r` are `Zero()`, and Expected asks for `ab`, `ac`, `Times(Zero(), b, ab)`, `Times(Zero(), c, ac)` and `Plus(ab, ac, Zero())`. Zero times anything is zero.",
      "With the caret in the `TimesSucc` branch, Scope shows `t3 : Times(a1, bc, r1)` and `p1 : Plus(r1, bc, r)`: a1 × (b + c) = r1 and r1 + (b + c) = r. The recursive call gives `ab1` and `ac1` with a1 × b = ab1, a1 × c = ac1 and ab1 + ac1 = r1. Until the `sorry` is replaced, Scope marks what the call returns as tainted, as on the previous page.",
      "What is left is arithmetic on `Plus` alone. From (ab1 + ac1) + (b + c) = r, `exchange` produces `ab` and `ac` with ab1 + b = ab, ac1 + c = ac and ab + ac = r. The first two are the last fields `TimesSucc` needs to build `Times(Succ(a1), b, ab)` and `Times(Succ(a1), c, ac)`.",
      "`exchange`, in the fourth box, shows that (w + y) + (x + z) = (w + x) + (y + z). It has no recursion of its own: it chains associativity in both directions (`plusAssoc`, and `plusAssocRev`, proved by recursion on its second piece of evidence) and commutativity, all from the boxes above it.",
      "Each `let` in `exchange` writes the type of every value it binds, and the checker checks each type against the result it names. A type can mention a binder before it in the same `let`, such as `yxz`. A binder used that way needs a type of its own, which is why `yxz` carries `: Nat()`. Put the caret on each line of `exchange` and compare Scope with these types."),
    task: "Replace the `sorry(_)` in the `TimesZero` branch, until the status line reads \"No sorry\" and \"Goal proved\".",
    refs: "§6, §7, §8, §9, §12, §13",
    boxes: [box(nat, plusRel, times), box(plusZeroRight, plusSucc, plusComm), box(plusAssoc, plusAssocRev), exchange,
      timesDistribGoal],
    initial: `-- Replace the sorry(_) in the TimesZero branch.
${withQed(timesDistrib(gap), "timesDistrib")}`,
    requireQed: true,
    solution: withQed(timesDistrib(`
      (Zero(), Zero(), TimesZero(b), TimesZero(c), PlusZero(Zero()))`), "timesDistrib"),
  },
] };
