// Solver verdict: silent diagnostics (1 UNSUPPORTED: `x` declares no initializer to check).
declare const x: number | string;
if (typeof x === "string") {
  const greeting: string = x;
}
