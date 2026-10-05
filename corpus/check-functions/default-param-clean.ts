// Solver verdict: silent — the literal-defaulted parameter checks like its
// declared type (P070), so the matching use stays clean (oracle clean).
function fromDefault(n: number = 1): number {
  const x: number = n;
  return 1;
}
