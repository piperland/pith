// Solver verdict: silent calls (A, B, C bind from each literal) + 1 UNSUPPORTED (body).
function tri<A, B, C>(x: A, y: B, z: C): A {
  return x;
}
const a = tri(1, "s", true);
