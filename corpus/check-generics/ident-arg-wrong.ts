// Solver verdict: 1x PITH2345 (inferred `number` from the annotated source vs the constraint) + 1 UNSUPPORTED (body).
function idc<T extends string>(x: T): T {
  return x;
}
const a: number = 1;
idc(a);
