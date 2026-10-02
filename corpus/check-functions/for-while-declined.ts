// Solver verdict: UNSUPPORTED (`while` loops stay declined: the oracle is
// clean on this body while the subset records one note with the
// frontend's recorded reason).
function countdown(n: number): number {
  while (n > 0) {
    return 1;
  }
  return 2;
}
