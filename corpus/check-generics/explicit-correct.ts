// Solver verdict: silent calls (explicit `number` matches) + 1 UNSUPPORTED (pass-through body declines).
function id<T>(x: T): T {
  return x;
}
const a = id<number>(1);
