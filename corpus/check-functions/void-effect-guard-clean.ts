// Solver verdict: silent (guard-effect join; oracle clean — the :void
// annotation accepts the bare arm return while the allowlist arm emits
// nothing and the bare tail checks trivially).
function guardWarn(drop: boolean): void {
  if (drop) {
    console.warn("dropping");
    return;
  }
  return;
}
