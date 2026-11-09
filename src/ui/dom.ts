export type Child = Node | string | null | undefined | false | Child[];

type Attr = string | boolean | ((event: Event) => void);

const flat = (children: Child[]): (Node | string)[] =>
  children.flatMap(c => Array.isArray(c) ? flat(c) : c === null || c === undefined || c === false ? [] : [c]);

export function h<K extends keyof HTMLElementTagNameMap>(tag: K, attrs: Record<string, Attr> = {},
    ...children: Child[]): HTMLElementTagNameMap[K] {
  const el = document.createElement(tag);
  for (const [key, value] of Object.entries(attrs)) {
    if (typeof value === "function") el.addEventListener(key.slice(2), value);
    else if (value === true) el.setAttribute(key, "");
    else if (value !== false) el.setAttribute(key, value);
  }
  el.append(...flat(children));
  return el;
}

export const fill = (el: Element, ...children: Child[]): void => el.replaceChildren(...flat(children));

export const load = (key: string): string | null => {
  try { return localStorage.getItem(`pledge:${key}`); } catch { return null; }
};

export const save = (key: string, value: string): void => {
  try { localStorage.setItem(`pledge:${key}`, value); } catch { }
};
