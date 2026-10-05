// Solver verdict: silent call (explicit `number` matches the resolved identifier kind) + 1 UNSUPPORTED (body).
function id<T>(x: T): T {
  return x;
}
const numIdent = 1;
id<number>(numIdent);
