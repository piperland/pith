// Solver verdict: clean oracle + 1 UNSUPPORTED (a local value shadows the
// alias, so the use declines instead of hijacking the value binding).
type Alias = number;
const Alias: string = "hello";
const n: Alias = 1;
