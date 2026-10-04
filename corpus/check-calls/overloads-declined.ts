// Solver verdict: 1x PITH2554 (both overload signatures admit exactly one
// argument; two arguments match none — the union arity diagnostic).
function over(a: number): number;
function over(a: string): string;
function over(a: any): any {
  return 1;
}
over(1, 2);
