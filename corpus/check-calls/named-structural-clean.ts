// Solver verdict: silent (the object arg checks member-wise against the
// local shape — pinned oracle match).
interface Point { x: number; y: string; }
function show(p: Point): number {
  return 1;
}
show({ x: 1, y: "ok" });
