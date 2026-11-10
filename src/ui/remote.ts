import type { CheckResult } from "../api.ts";
import type { Phase } from "../syntax.ts";
import type { NameKind } from "./editor.ts";

type Queries = Pick<CheckResult, "infoAt" | "nameAt" | "explainAt" | "evalAt">;

export type Summary = Omit<CheckResult, keyof Queries> & { kinds: [offset: number, kind: NameKind | null][] };

export type Checker = Queries & { check(texts: string[], phase: Phase): Summary };

export interface Request { id: number; method: keyof Checker; args: unknown[] }

export type Reply = { id: number } & ({ value: unknown } | { error: string });

export const LAZY = "()";

export interface Remote {
  call<M extends keyof Checker>(method: M, ...args: Parameters<Checker[M]>): Promise<ReturnType<Checker[M]>>;
  close(): void;
}

const decode = (v: unknown): unknown => Array.isArray(v) ? v.map(decode)
  : !v || typeof v !== "object" ? v
    : LAZY in v ? (lazy => () => lazy)(decode(v[LAZY]))
      : Object.fromEntries(Object.entries(v).map(([key, x]) => [key, decode(x)]));

export function remote(): Remote {
  const worker = new Worker(new URL("./worker.ts", import.meta.url), { type: "module" });
  const waiting = new Map<number, { resolve: (value: never) => void; reject: (error: string) => void }>();
  let next = 0;
  worker.onmessage = ({ data }: MessageEvent<Reply>) => {
    const { resolve, reject } = waiting.get(data.id)!;
    waiting.delete(data.id);
    if ("error" in data) reject(data.error);
    else resolve(decode(data.value) as never);
  };
  worker.onerror = e => {
    for (const { reject } of waiting.values()) reject(e.message ?? "the checker could not be loaded");
    waiting.clear();
  };
  return {
    call: (method, ...args) => new Promise((resolve, reject) => {
      waiting.set(next, { resolve, reject });
      worker.postMessage({ id: next++, method, args } satisfies Request);
    }),
    close: () => worker.terminate(),
  };
}
