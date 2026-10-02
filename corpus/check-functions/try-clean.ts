// Solver verdict: SILENT (try/catch arms plus a clean tail return, each
// checked independently through the join path).
function fetchCount(flag: boolean): number {
  try {
    return 1;
  } catch {
    return 2;
  }
  return 3;
}
