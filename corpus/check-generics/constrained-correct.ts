// Solver verdict: silent calls (inferred `string` satisfies; explicit `string` satisfies and matches) + 1 UNSUPPORTED (body).
function idc<T extends string>(x: T): T {
  return x;
}
const a = idc("s");
const b = idc<string>("s");
