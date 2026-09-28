// Solver verdict: one PITH2322 (oracle TS2322) on the body against `T`; the `f(1)` call infers cleanly.
function f<T>(x: T): T {
  return "s";
}
const a = f(1);
