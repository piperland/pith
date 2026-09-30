// Solver verdict: silent calls (explicit `number, string` match) + 1 UNSUPPORTED (pass-through body declines).
function pair<T, U>(x: T, y: U): T {
  return x;
}
const a = pair<number, string>(1, "s");
