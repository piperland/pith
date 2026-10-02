// Solver verdict: silent (throw-only body; oracle clean — no
// missing-return family under --strict, and the throw accepts any value).
function onlyThrow(): number {
  throw new Error("x");
}
