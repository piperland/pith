// Solver verdict: one PITH2345 (oracle TS2345) at the mismatched second argument + 1 UNSUPPORTED (body).
function pair<T, U>(x: T, y: U): T {
  return x;
}
const a = pair<number, string>(1, true);
