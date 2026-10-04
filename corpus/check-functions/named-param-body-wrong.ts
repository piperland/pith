// Solver verdict: 1x PITH2322 (named params admit; the wrong literal
// body still reports).
interface Point { x: number; }
function locate(p: Point): number {
  return "oops";
}
