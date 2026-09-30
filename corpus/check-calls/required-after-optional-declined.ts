// Solver verdict: UNSUPPORTED (required-after-optional: tsc errors the
// declaration with TS1016 and checks calls at the exact total — the solver
// spells no declaration diagnostics). Pinned divergence: the oracle reports
// TS1016 while the solver declines with one note.
function r(a?: number, b: number): number {
  return 1;
}
r(1, 2);
