// Solver verdict: UNSUPPORTED (nested guards are outside the subset); the
// oracle is silent here (`never`), so the differential records a decline.
declare const x: number | string;
if (typeof x === "string") {
  if (typeof x === "number") {
    const count: number = x;
  }
}
