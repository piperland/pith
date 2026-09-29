// Solver verdict: 1 UNSUPPORTED (keyof parameter); oracle 1x TS2322 on the body.
function pick<T>(x: keyof T): T {
  return x;
}
const a = pick("s");
