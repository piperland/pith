// Solver verdict: clean oracle + 1 UNSUPPORTED (chained aliases expand one
// level only; tsc resolves transitively).
type A = number;
type B = A;
const b: B = 1;
