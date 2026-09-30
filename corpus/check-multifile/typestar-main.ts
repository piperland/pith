// Solver verdict: one PITH2322 (oracle TS2322) at the wrong member;
// the star-barrel alias checks clean through the same expansion.
import { Point, Alias } from "./typestar-index";
const ok: Alias = { x: 1, y: 2 };
const wrong: Point = { x: 1, y: "oops" };
