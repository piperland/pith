// Solver verdict: silent call (T and U bind per identifier position) + 1 UNSUPPORTED (body).
function pair<T, U>(x: T, y: U): T {
  return x;
}
const a = 1;
pair(a, a);
