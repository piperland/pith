// Solver verdict: 1x PITH2345 (the compatible signature checks exactly
// like a lone declaration - the implementation signature never
// participates, so `true` reports against `number` rather than matching
// the `any` implementation).
function im(a: number): number;
function im(a: any): any {
  return 1;
}
im(1);
im(true);
