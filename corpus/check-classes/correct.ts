// Solver verdict: silent (property inits match, ctor arity and arg types match).
class C {
  x: number = 1;
  s: string = "ok";
  constructor(a: number) {}
}
const c = new C(1);
