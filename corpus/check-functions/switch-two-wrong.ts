// Solver verdict: DIAGNOSED TWICE (two wrong case returns; oracle 2x
// TS2322, one per case arm, each checked independently).
function pick(n: number): number {
  switch (n) {
    case 1:
      return "a";
    case 2:
      return "b";
    default:
      return 3;
  }
}
