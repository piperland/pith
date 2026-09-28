// Solver verdict: 3x UNSUPPORTED (computed member `A`). tsc folds the
// computed value (`A` is `10`) and stays clean — pinned divergence.
const K = 10;
enum Comp { A = K, B = 1 }
const p: Comp = 10;
const q: Comp = Comp.A;
const r: Comp = 1;
