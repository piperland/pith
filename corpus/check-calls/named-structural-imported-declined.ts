// Solver verdict: 1 UNSUPPORTED (the imported name claims no local shape,
// so the call keeps the legacy decline; the oracle checks it — pinned
// divergence).
import { Point } from "./named-structural-imported-dep";
function show(p: Point): number {
  return 1;
}
show({ x: "oops" });
