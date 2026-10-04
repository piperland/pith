// Solver verdict: UNSUPPORTED (else-if chain nested inside a branch;
// oracle clean — nesting needs flow facts the subset refuses — so the
// solver records one note with the nested-chain reason, never a partial
// verdict).
function pick(flag: boolean, other: boolean, third: boolean): number {
  if (flag) {
    if (other) {
      return 1;
    } else if (third) {
      return 2;
    } else {
      return 3;
    }
  } else {
    return 4;
  }
}
