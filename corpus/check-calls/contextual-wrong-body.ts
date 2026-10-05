function apply(f: (x: number) => number): number {
  return 1;
}
function apply2(f: (x: number, y: string) => number): number {
  return 1;
}
apply((x) => "oops");
apply2((x, y) => y);
