function arity(a: number): number;
function arity(a: number, b: number, c: number): number;
function arity(...args: any[]): any {
  return 1;
}
arity();
arity(1, 2, 3, 4);
arity(1, 2);
