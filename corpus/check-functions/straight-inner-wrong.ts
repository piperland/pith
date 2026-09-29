// Solver verdict: DIAGNOSED (wrong inner declarators report per position).
function early(n: number): number {
  const x: number = "oops";
  return 1;
}
function later(n: number): number {
  const a: number = 1;
  const b: string = 2;
  const c: boolean = true;
  return 1;
}
function pair(n: number): number {
  const a: number = "x", b: string = "ok";
  return 1;
}
