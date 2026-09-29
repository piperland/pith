// Solver verdict: DIAGNOSED once (nested straight blocks flatten; only
// the wrong inner declarator reports).
function boxed(n: number): number {
  const a: number = 1;
  {
    const b: string = 2;
  }
  return 1;
}
function lone(n: number): number {
  {
    return 1;
  }
}
