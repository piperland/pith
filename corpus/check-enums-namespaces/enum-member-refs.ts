// Solver verdict: 5x PITH2322 (`5`, cross-enum `Color.Red` and
// `Color.Green`, `"a"`, `true`). Same-enum dot/bracket refs (including the
// string-enum `Str.A`) stay silent. Unknown members, numeric indices, and
// calls decline distinctly instead (unit-pinned: tsc spells TS2339,
// `Type 'string'`, and TS2349 there — families the subset never forces).
enum Color { Red, Green, Blue }
enum Other { Zero }
enum Str { A = "a", B = "b" }
const a: Color = Color.Red;
const b: Color = Color["Green"];
const c: Color = 5;
const d: Other = Color.Red;
const e: Other = Color["Green"];
const f: Str = Str.A;
const g: Str = "a";
const h: Color = true;
