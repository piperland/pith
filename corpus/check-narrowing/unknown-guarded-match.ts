// Solver verdict: silent diagnostics (1 UNSUPPORTED: `uv` declares no initializer to check).
declare const uv: unknown;
if (typeof uv === "string") {
  const greeting: string = uv;
}
