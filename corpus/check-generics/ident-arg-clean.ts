// Solver verdict: silent calls (T binds per identifier: the P060-inferred kind and the annotated kind) + 1 UNSUPPORTED (body).
function id<T>(x: T): T {
  return x;
}
const a = 1;
const b: string = "s";
id(a);
id(b);
