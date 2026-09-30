// Solver verdict: silent (range arity 1-2 admits every call, including
// explicit `undefined` at the optional position). The oracle is clean.
function opt(a: number, b?: number): number {
  return 1;
}
opt(1);
opt(1, 2);
opt(1, undefined);
function dflt(a: number, b: number = 2): number {
  return 1;
}
dflt(1);
dflt(1, 2);
