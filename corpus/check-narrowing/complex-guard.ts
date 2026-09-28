// Solver verdict: UNSUPPORTED (disjunctions are outside the subset); the
// oracle still diagnoses the full union, so the differential records a
// decline, never a matching diagnostic.
declare const x: number | string;
if (typeof x === "number" || typeof x === "string") {
  const count: number = x;
}
