// Solver verdict: 1x PITH2322 (cross-enum return) + 2x UNSUPPORTED
// (computed/ambient member returns stay declined while tsc folds and
// accepts them — pinned divergences). Same-enum dot/bracket returns stay
// silent. Unknown members decline distinctly instead (unit-pinned: tsc
// spells TS2339 there — a family the subset never forces).
enum Color { Red = 0, Green = 1 }
enum Other { Zero = 0 }
const K = 10;
enum Comp { A = K, B = 1 }
declare enum Amb { A }
function f(): Color { return Color.Red; }
function g(): Color { return Color["Green"]; }
function h(): Other { return Color.Red; }
function p(): Comp { return Comp.B; }
function q(): Amb { return Amb.A; }
