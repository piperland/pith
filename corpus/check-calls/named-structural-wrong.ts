// Solver verdict: 3x PITH2322 at the argument spans (one per wrong member,
// first-mismatch stops each call — pinned oracle match).
interface Point { x: number; y: string; }
function show(p: Point): number {
  return 1;
}
show({ x: "oops", y: "ok" });
show({ x: "oops", y: 42 });
