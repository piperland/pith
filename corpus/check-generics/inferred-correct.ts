// Solver verdict: silent calls (T binds from each literal) + 1 UNSUPPORTED (body).
function id<T>(x: T): T {
  return x;
}
const a = id(1);
const b = id("s");
