// Solver verdict: 1x PITH2322. `const enum` checks identically to plain
// enums (probed tsc 7.0.2) — noted, never forked; the member access `CE.X`
// resolves silently through the P053 member-reference facts.
const enum CE { X, Y }
const t: CE = 0;
const v: CE = 7;
const w: CE = CE.X;
