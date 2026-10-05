// Solver verdict: 1x PITH2345 (explicit `string` vs the resolved `number` identifier kind) + 1 UNSUPPORTED (body).
function id<T>(x: T): T {
  return x;
}
const numIdent = 1;
id<string>(numIdent);
