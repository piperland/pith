// Solver verdict: one PITH2322 (oracle TS2322) on `count` in the guarded region.
declare const x: number | string;
if (typeof x === "string") {
  const count: number = x;
}
