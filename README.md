# Pledge

A language for teaching restricted dependent types, loosely based on
[Sleight](https://github.com/emmarion/sleight). It runs in a web browser;
[DESIGN.md](DESIGN.md) describes the language and
[SOUNDNESS.md](SOUNDNESS.md) argues that it is sound.

The implementation is TypeScript with no dependencies beyond the
compiler. To run it locally:

```sh
npm install
npm run build
npm run serve      # then open http://localhost:8000/
npm test
```

`web/index.html` is the main page (DESIGN.md §13) and `web/tutorial.html`
the tutorial (§12). The workflow in `.github/workflows/` deploys `web/`
to GitHub Pages once Pages is enabled for the repository. The code was
written by Claude sessions; [ASSUMPTIONS.md](ASSUMPTIONS.md) lists the
choices they made where DESIGN.md is silent, and
[INTERNALS.md](INTERNALS.md) describes how the code is laid out.
