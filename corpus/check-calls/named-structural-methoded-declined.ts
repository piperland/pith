// Solver verdict: 1 UNSUPPORTED (method members carry no value-type facts,
// so the shape declines inside the shared comparison; the oracle is clean
// here — pinned divergence).
interface Svc { x: number; run(n: number): void; }
function show(p: Svc): number {
  return 1;
}
show({ x: 1, run(n) { } });
