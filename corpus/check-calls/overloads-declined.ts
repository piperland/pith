// Solver verdict: UNSUPPORTED (three declarations of one name; overload
// resolution is future work). The oracle reports TS2554 here — pinned divergence.
function over(a: number): number;
function over(a: string): string;
function over(a: any): any {
  return 1;
}
over(1, 2);
