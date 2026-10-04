// Solver verdict: SILENT (else-if chain branches, each checked
// independently through the join path).
function pick(flag: boolean, other: boolean): number {
  if (flag) {
    return 1;
  } else if (other) {
    return 2;
  } else {
    return 3;
  }
}
