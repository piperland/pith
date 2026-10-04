// Solver verdict: 2 UNSUPPORTED (unresolvable identifier decline + body); oracle errors TS2304.
function id<T>(x: T): T {
  return x;
}
id(nope);
