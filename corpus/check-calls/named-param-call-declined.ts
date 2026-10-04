// Solver verdict: 1x PITH2345 (primitive params still check) + 1
// UNSUPPORTED (the call against the opaque named param declines
// distinctly; the oracle is clean there — pinned divergence).
interface Point { x: number; }
function show(p: Point): number {
  return 1;
}
function add(a: number, b: number): number {
  return 1;
}
show({ x: 1 });
add("oops", 2);
