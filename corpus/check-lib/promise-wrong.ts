// Solver verdict: 4x PITH2322 (oracle TS2322) — one per wrong return,
// including through `Promise<Array<...>>` member-wise and `await`.
async function getCount(): Promise<number> {
  return "oops";
}
async function getName(): Promise<string> {
  return 1;
}
async function getIds(): Promise<Array<number>> {
  return ["oops"];
}
async function getBadAwaited(): Promise<number> {
  return await "oops";
}
