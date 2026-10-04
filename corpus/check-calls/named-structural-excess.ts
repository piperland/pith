// Solver verdict: 1x PITH2353 spelling the interface name (pinned
// oracle match).
interface Point { x: number; }
function show(p: Point): number {
  return 1;
}
show({ x: 1, extra: 2 });
