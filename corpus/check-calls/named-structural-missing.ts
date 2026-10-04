// Solver verdict: 1x PITH2741 + 1x PITH2739, both spelling the interface
// name (pinned oracle match).
interface Point { x: number; y: string; }
interface Big { a: number; b: string; c: boolean; }
function one(p: Point): number {
  return 1;
}
function many(p: Big): number {
  return 1;
}
one({ x: 1 });
many({ a: 1 });
