// Solver verdict: SILENT (plain catch binding admits structurally; `e`
// unused, so both arms check as literal positions through the join path).
function fetchCount(flag: boolean): number {
  try {
    return 1;
  } catch (e) {
    return 2;
  }
}
