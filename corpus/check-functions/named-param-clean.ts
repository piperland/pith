// Solver verdict: silent (interface/alias/primitive params admit as
// opaque; the literal body checks normally).
interface Point { x: number; }
type Label = string;
function locate(p: Point, tag: Label, n: number): number {
  return 1;
}
