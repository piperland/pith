// Solver verdict: 1x PITH2345 (inferred `boolean` against the `number` constraint) + 1 UNSUPPORTED (body).
function cpair2<T, U extends number>(x: T, y: U): T {
  return x;
}
const a = cpair2("s", true);
