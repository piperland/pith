// Solver verdict: 2 UNSUPPORTED (pass-through body + no inference candidate for `T`); oracle clean.
function pair<T, U>(x: T, y: U): T {
  return x;
}
declare const u: number;
declare const v: string;
const a = pair(u, v);
