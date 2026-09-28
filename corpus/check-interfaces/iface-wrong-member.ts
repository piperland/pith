// Solver verdict: 2x PITH2322 (one per wrong member, literal order).
interface Point { x: number; label: string; }
const point: Point = { x: "oops", label: 42 };
