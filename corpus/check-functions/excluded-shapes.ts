// Solver verdict: silent, no function facts (arrows, function expressions,
// methods out of scope; oracle clean).
const double = (n: number): number => n;
let inc = function step(n: number): number {
  return n;
};
const obj = {
  pick(n: number): number {
    return n;
  },
};
class Box {
  get(n: number): number {
    return n;
  }
}
