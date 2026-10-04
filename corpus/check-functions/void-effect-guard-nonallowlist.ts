// Solver verdict: UNSUPPORTED (direct call in the guard arm — only P024
// allowlist member calls admit as effects; oracle clean on both decls).
function helper(key: string): void {
  console.warn(key);
}
function guardHelper(key: string, drop: boolean): void {
  if (drop) {
    helper(key);
    return;
  }
  return;
}
