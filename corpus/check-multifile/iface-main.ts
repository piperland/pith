// Solver verdict: one PITH2322 (oracle TS2322) at the wrong member,
// one PITH2741 (oracle TS2741) spelling the underlying interface.
import { Point } from "./iface-mid";
const ok: Point = { x: 1, y: 2 };
const wrong: Point = { x: 1, y: "oops" };
const missing: Point = { x: 1 };
