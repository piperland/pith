// Solver verdict: one PITH2322 (oracle TS2322) after the early-return guard;
// the matching use refines and stays silent.
declare const x: number | string;
function gate(): void {
  if (typeof x !== "string") return;
  const greeting: string = x;
  const count: number = x;
}
