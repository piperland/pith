// Solver verdict: UNSUPPORTED (a const between the guards breaks the run;
// oracle clean — interleaved statements need flow facts the subset
// refuses, so the whole declaration declines, never a partial verdict).
function mixed(a: boolean, b: boolean, c: boolean): number {
  if (a) return 1;
  if (b) return 2;
  const x: number = 3;
  if (c) return 3;
  return 4;
}
