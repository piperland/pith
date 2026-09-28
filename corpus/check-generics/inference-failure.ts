// Solver verdict: 2 UNSUPPORTED (pass-through body + no inference candidate for `u`); oracle clean.
function id<T>(x: T): T {
  return x;
}
declare const u: number;
const a = id(u);
