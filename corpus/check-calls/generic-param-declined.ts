// Solver verdict: silent + 1 UNSUPPORTED (generic T params decline
// exactly as before; the oracle is clean — pinned divergence).
function identity<T>(x: T): T {
  return x;
}
identity(1);
