// Solver verdict: UNSUPPORTED (non-typeof conditions are outside the subset);
// the oracle still narrows and diagnoses, so the differential records a
// decline, never a matching diagnostic.
declare const x: number | string;
if (x === "hi") {
  const count: number = x;
}
