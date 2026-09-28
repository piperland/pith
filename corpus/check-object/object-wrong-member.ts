// Solver verdict: four PITH2322 (oracle TS2322): a const wrong member, a let
// wrong member, plus both primitive/object cross-shapes.
const point: { x: number; label: string } = { x: "oops", label: "ok" };
let count: { total: number } = { total: true };
const crossPrimitive: number = { a: 1 };
const crossObject: { a: number } = 1;
