import { defineConfig } from "vite";

const recover = () => {
  const key = "pledge-reloaded";
  const storage = f => { try { return f(sessionStorage); } catch { return "1"; } };
  let failed = false;
  addEventListener("error", e => {
    if (failed || !e.target.matches?.("script, link[rel=stylesheet]")) return;
    failed = true;
    if (!storage(s => s.getItem(key)) && !storage(s => s.setItem(key, "1"))) return location.reload();
    storage(s => s.removeItem(key));
    const show = () => document.body.innerHTML =
      "<main class=\"fallback\"><p>Pledge could not load all of its files. Reload the page to try again.</p></main>";
    document.readyState === "loading" ? addEventListener("DOMContentLoaded", show) : show();
  }, true);
  addEventListener("load", () => failed || storage(s => s.removeItem(key)));
};

export default defineConfig({
  root: "web",
  base: "./",
  build: {
    outDir: "../dist",
    emptyOutDir: true,
    sourcemap: true,
    rollupOptions: { input: ["web/index.html", "web/tutorial.html"] },
  },
  plugins: [{
    name: "recover",
    transformIndexHtml: html => html.replace(/<meta charset="utf-8">/, m => `${m}\n<script>(${recover})();</script>`),
  }],
});
