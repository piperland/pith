// Solver verdict: silent call (unresolvable identifier keeps the explicit-path skip; oracle errors TS2304) + 1 UNSUPPORTED (body).
function id<T>(x: T): T {
  return x;
}
id<string>(nope);
