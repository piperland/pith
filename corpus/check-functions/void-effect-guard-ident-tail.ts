// Solver verdict: DIAGNOSED (guard-effect join with a bare-identifier
// tail; oracle TS2322 on the tail — the name resolves one level through
// P048 to the string parameter, then checks like a literal).
function guardIdent(key: string, drop: boolean): void {
  if (drop) {
    console.warn(key);
    return;
  }
  return key;
}
