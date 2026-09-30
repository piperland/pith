// Solver verdict: silent calls (T binds from each literal) + 1 UNSUPPORTED (body).
function pair<T, U>(x: T, y: U): T {
  return x;
}
const a = pair(1, "s");
