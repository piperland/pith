// Solver verdict: 1x PITH2345 (inferred `number` against the `string` constraint) + 1 UNSUPPORTED (body).
function cpair<T extends string, U>(x: T, y: U): T {
  return x;
}
const a = cpair(1, "s");
