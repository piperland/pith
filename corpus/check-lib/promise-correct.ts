// Solver verdict: silent — async returns carry the unwrapped payload type
// (`await` is transparent, exactly like tsc).
async function getCount(): Promise<number> {
  return 1;
}
async function getName(): Promise<string> {
  return "ok";
}
async function getIds(): Promise<Array<number>> {
  return [1, 2];
}
async function getAwaited(): Promise<number> {
  return await 1;
}
