// Solver verdict: silent + 2 UNSUPPORTED (P060: written `: RegExp` is
// lib-declined — tsc is clean on `r` and spells TS2322 on `s`, pinned
// divergences, never forced verdicts).
const r: RegExp = /x/;
const s: RegExp = "x";
