// Solver verdict: 2x PITH2694 (missing + hidden) + PITH2709 (bare
// namespace) + PITH2749 (trailing namespace) + PITH2713 (past a type).
namespace NS { export enum Dir { Up, Down } interface Hidden { x: number; } export interface Point { x: number; } }
namespace Outer { export namespace Inner { export const V = 2; } }
const a: NS.Nope = 1;
const h: NS.Hidden = 0;
const n: NS = 1;
const m: Outer.Inner = 1;
const q: NS.Point.X = 1;
