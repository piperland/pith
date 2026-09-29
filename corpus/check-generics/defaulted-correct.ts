// Solver verdict: silent calls (inferred `number`; explicit `string` overrides the default) + 1 UNSUPPORTED (body).
function idd<T = number>(x: T): T {
  return x;
}
const a = idd(1);
const b = idd<string>("s");
