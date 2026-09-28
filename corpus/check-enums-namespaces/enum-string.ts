// Solver verdict: 5x PITH2322 (`"a"`, `"z"`, `1`, `undefined`, `null`)
// + 1x UNSUPPORTED (member access).
enum Str { A = "a", B = "b" }
const g: Str = "a";
const h: Str = "z";
const i: Str = Str.A;
const j: Str = 1;
const u: Str = undefined;
const n: Str = null;
