// Solver verdict: 4x UNSUPPORTED (computed members `A`, `Y`). tsc folds
// computed values and stays clean — pinned divergence (no const-eval
// beyond recorded member values).
const K = 10;
enum Comp { A = K, B = 1 }
enum Cross { X = 1, Y = X }
const p: Comp = Comp.B;
const q: Comp = Comp["B"];
const r: Cross = Cross.Y;
const s: Cross = Cross["X"];
