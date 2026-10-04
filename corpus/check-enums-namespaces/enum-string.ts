// Solver verdict: 5x PITH2322 (`"a"`, `"z"`, `1`, `undefined`, `null`).
// The member access `Str.A` resolves silently through the P053
// member-reference facts.
enum Str { A = "a", B = "b" }
const g: Str = "a";
const h: Str = "z";
const i: Str = Str.A;
const j: Str = 1;
const u: Str = undefined;
const n: Str = null;
