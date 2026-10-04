// Solver verdict: UNSUPPORTED (guards with no tail return; oracle TS2366
// — the subset has no declaration-completeness family, so the checkable
// guards stay silent plus one note, never a partial verdict).
function openChain(a: boolean, b: boolean): number {
  if (a) return 1;
  if (b) return 2;
}
