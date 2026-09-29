// Solver verdict: 1 UNSUPPORTED (mapped return); oracle 1x TS2353 on the body.
function mapped<T>(x: T): { [K in keyof T]: T[K] } {
  return { v: 1 };
}
const a = mapped(1);
