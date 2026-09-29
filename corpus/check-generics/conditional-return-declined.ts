// Solver verdict: 1 UNSUPPORTED (conditional return); oracle 1x TS2322 on the body.
function cond<T>(x: T): T extends string ? string : number {
  return 1;
}
const a = cond("s");
