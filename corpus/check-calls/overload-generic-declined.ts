// Solver verdict: UNSUPPORTED on the second call (the generic signature is
// excluded with its own reason, so no checkable signature admits `true`).
// The oracle reports TS2769 there — pinned divergence.
function g<T extends string>(a: T): T;
function g(a: number): number;
function g(a: any): any {
  return a;
}
g(1);
g(true);
