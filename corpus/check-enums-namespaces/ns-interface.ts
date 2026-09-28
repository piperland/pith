// Solver verdict: 1x PITH2741 + 1x PITH2353 + 1x PITH2322 (all spelling
// `Point`) + 1x UNSUPPORTED (namespace-qualified value).
namespace NS { export interface Point { x: number; y: string; } export const VAL = 1; }
const p1: NS.Point = { x: 1 };
const p2: NS.Point = { x: 1, y: "s" };
const p3: NS.Point = { x: 1, y: "s", extra: true };
const p4: NS.Point = { x: "s", y: "t" };
const y: number = NS.VAL;
