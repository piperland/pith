// Solver verdict: one PITH2322 (oracle TS2322) at the wrong member (P052:
// chained interfaces check with the UNDERLYING display; tsc agrees).
interface Point {
  x: number;
  y: number;
}
type A = Point;
type B = A;
const ok: B = { x: 1, y: 2 };
const wrong: B = { x: 1, y: "oops" };
