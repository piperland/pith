// Solver verdict: UNSUPPORTED (missing terminal else; oracle TS2366 —
// exhaustiveness needs a declaration-completeness family the subset
// refuses — so the checkable branches stay silent plus one note, never a
// forced verdict).
function pick(flag: boolean, other: boolean): number {
  if (flag) {
    return 1;
  } else if (other) {
    return 2;
  }
}
