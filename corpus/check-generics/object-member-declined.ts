// Solver verdict: 1 UNSUPPORTED (object return); oracle 1x TS2322 on the body.
function f<T>(x: T): { v: T } {
  return x;
}
const a = f(1);
