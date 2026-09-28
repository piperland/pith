// Solver verdict: silent (every member matches; `let` checks like `const`).
interface Point { x: number; label: string; }
interface Flags { done: boolean; nully: null; undef: undefined; }
const point: Point = { x: 1, label: "ok" };
const flags: Flags = { done: false, nully: null, undef: undefined };
let movable: Point = { x: 2, label: "go" };
