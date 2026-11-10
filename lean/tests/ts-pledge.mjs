#!/usr/bin/env node
import { readFileSync } from "node:fs";
import { verdict } from "./verdict.mjs";

const [, , command, flag, phase, file] = process.argv;
if (command !== "check" || flag !== "--phase" || !file) throw new Error("usage: ts-pledge.mjs check --phase N FILE");
console.log(JSON.stringify(verdict(readFileSync(file, "utf8"), Number(phase))));
