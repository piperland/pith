// Solver verdict: silent (every object shape matches; `let` checks like `const`).
const point: { x: number; label: string } = { x: 1, label: "ok" };
const flags: { done: boolean; nully: null; undef: undefined } = { done: false, nully: null, undef: undefined };
let movable: { x: number } = { x: 2 };
