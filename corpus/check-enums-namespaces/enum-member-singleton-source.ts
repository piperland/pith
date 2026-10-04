// Solver verdict: 3x PITH2322 (single-member sources spell the enum
// alone — `Other.Zero` spells `Type 'Other'`, `Solo.Only` spells
// `Type 'Solo'` — while multi-member `Color.Red` still spells
// `Type 'Color.Red'`). Same-enum singleton refs stay silent.
enum Other { Zero }
enum Solo { Only = "only" }
enum Color { Red, Green }
const a: Other = Other.Zero;
const b: Color = Other.Zero;
const c: Color = Solo.Only;
const d: Other = Color.Red;
