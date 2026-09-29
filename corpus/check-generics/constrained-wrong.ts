// Solver verdict: 1x PITH2345 (inferred `number` against the constraint) + 1x PITH2344 (explicit `number` violates) + 1 UNSUPPORTED (body).
function idc<T extends string>(x: T): T {
  return x;
}
const a = idc(1);
const b = idc<number>("s");
