// Solver verdict: SILENT (P082 same-file direct callee: `helper` is one
// void-annotated declaration with one required param and the arm passes
// exactly one argument, so the direct call admits as an effect).
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
