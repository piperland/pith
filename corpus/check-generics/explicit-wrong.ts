// Solver verdict: one PITH2345 (oracle TS2345) at the mismatched argument + 1 UNSUPPORTED (body).
function id<T>(x: T): T {
  return x;
}
const a = id<number>("oops");
