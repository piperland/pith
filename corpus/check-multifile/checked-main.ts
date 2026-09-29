// Solver verdict: one PITH2322 (oracle TS2322) at the declarator,
// one PITH2345 (oracle TS2345) at the mismatched argument;
// imported interface/enum annotations check clean.
import { LIMIT, NAME, isEven } from "./checked-utils";
import { Point, Color, ORIGIN_X } from "./checked-types";
const n: number = LIMIT;
const bad: number = NAME;
isEven(2);
isEven("oops");
const p: Point = { x: 1, y: 2 };
const c: Color = 1;
const x: number = ORIGIN_X;
