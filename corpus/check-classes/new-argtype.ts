// Solver verdict: one PITH2345 (oracle TS2345) at the mismatched argument.
class C {
  constructor(a: number, b: number) {}
}
const c = new C("oops", 2);
