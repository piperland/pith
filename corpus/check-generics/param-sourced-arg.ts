// Solver verdict: silent call (T binds from the enclosing parameter) + 1 UNSUPPORTED (pass-through body; `wrap` is non-generic).
function id<T>(x: T): T {
  return x;
}
function wrap(p: number) {
  return id(p);
}
