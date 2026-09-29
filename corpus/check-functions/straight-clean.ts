// Solver verdict: silent (straight bodies check per position; oracle clean).
function headed(n: number): number {
  const x: number = 1;
  return 1;
}
function inferred(n: number): number {
  const x = 1;
  let y: number = 2;
  return 3;
}
function nested(n: number): number {
  function half(m: number): number {
    return 1;
  }
  return 1;
}
