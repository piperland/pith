// Solver verdict: 1 UNSUPPORTED (multiple type parameters); the call skips. Oracle clean.
function pair<T, U>(x: T, y: U): T {
  return x;
}
const a = pair(1, "s");
