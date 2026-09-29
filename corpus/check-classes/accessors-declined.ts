// Solver verdict: UNSUPPORTED (accessors are outside the subset; oracle TS2322).
class C {
  get x(): number {
    return "oops";
  }
}
