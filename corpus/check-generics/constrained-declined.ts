// Solver verdict: 1 UNSUPPORTED (constraint); oracle clean.
function idc<T extends string>(x: T): T {
  return x;
}
const a = idc("s");
