// Solver verdict: 1 UNSUPPORTED (union parameter); oracle 1x TS2322 on the body.
function f<T>(x: T | string): T {
  return x;
}
const a = f(1);
