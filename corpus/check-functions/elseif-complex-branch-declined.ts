// Solver verdict: UNSUPPORTED (else-if chain with a throw branch; oracle
// clean — throw positions outside guard-throw/straight shapes stay declined
// with a distinct recorded reason, never a partial verdict).
function pick(flag: boolean, other: boolean): number {
  if (flag) {
    return 1;
  } else if (other) {
    throw new Error("x");
  } else {
    return 3;
  }
}
