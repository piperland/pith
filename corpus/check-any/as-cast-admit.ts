// Solver verdict: two PITH2322 (oracle TS2322); admitted casts check on
// through the existing path (satisfies stays transparent to the operand,
// `as unknown` results spell `unknown`).
const n: number = (1 as number);
const s: string = (1 as number);
const u: number = ("x" as unknown);
const t: string = ("x" satisfies string);
