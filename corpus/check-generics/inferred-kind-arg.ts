// Solver verdict: 1x PITH2345 (inferred `number` from the unannotated P060-inferred source vs the constraint) + 1 UNSUPPORTED (body).
function idc<T extends string>(x: T): T {
  return x;
}
const a = 1;
idc(a);
