// Solver verdict: one PITH2322 (oracle TS2322) in the else region; the then
// region refines to the complement and stays silent.
declare const x: number | string;
if (typeof x !== "string") {
  const count: number = x;
} else {
  const other: number = x;
}
