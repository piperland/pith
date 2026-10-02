// Solver verdict: clean oracle + 1 UNSUPPORTED (generic aliases never
// instantiate; the `<`-head use declines instead of forcing a verdict).
type Box<T> = T;
const b: Box<number> = 1;
