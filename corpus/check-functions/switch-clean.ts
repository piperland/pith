// Solver verdict: SILENT (switch cases plus a clean default, each
// checked independently through the join path).
function pick(n: number): number {
  switch (n) {
    case 1:
      return 1;
    case 2:
      return 2;
    default:
      return 3;
  }
}
