// Solver verdict: UNSUPPORTED (valued return in the guard arm — only bare
// returns skip; oracle clean).
function guardValued(key: string, drop: boolean): number {
  if (drop) {
    console.warn(key);
    return 1;
  }
  return 2;
}
