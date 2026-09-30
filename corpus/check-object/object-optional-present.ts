// Solver verdict: 1x PITH2322 (present optional member checks like a
// required one) plus 1x PITH2741 (missing names only the required member,
// spelling `y?: number | undefined`); the fully-supplied object is silent.
const ok: { x: number; y?: number } = { x: 1, y: 2 };
const bad: { x: number; y?: number } = { x: 1, y: "oops" };
const miss: { x: number; y?: number } = {};
