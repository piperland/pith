// Solver verdict: 2x PITH2558 (oracle TS2558), one per call at each callee + 1 UNSUPPORTED (body).
function pair<T, U>(x: T, y: U): T {
  return x;
}
const a = pair<number>(1, "s");
const b = pair<number, string, boolean>(1, "s");
