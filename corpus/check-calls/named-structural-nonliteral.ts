// Solver verdict: 2 UNSUPPORTED (the identifier arg declines with its own
// reason, the call-result arg keeps the opaque decline; the oracle is
// clean on both — pinned divergences).
interface Point { x: number; }
function show(p: Point): number {
  return 1;
}
function make(): Point {
  return obj;
}
const obj: Point = { x: 1 };
show(obj);
show(make());
