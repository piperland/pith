// Solver verdict: 1 UNSUPPORTED (call sites thread no alias tables, so
// alias-named params keep the opaque decline; the oracle checks them —
// pinned divergence).
interface Point { x: number; y: string; }
type Alias = Point;
function show(p: Alias): number {
  return 1;
}
show({ x: "oops", y: "ok" });
