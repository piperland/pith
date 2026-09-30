// Solver verdict: two PITH2322 (oracle TS2322): one at the wrong alias
// member (the alias expands to the underlying interface), one at the wrong
// primitive-alias declarator (behaves exactly like its target spelling).
import { Alias, Num } from "./alias-mid";
const ok: Alias = { x: 1, y: 2 };
const wrong: Alias = { x: 1, y: "oops" };
const count: Num = 1;
const bad: Num = "oops";
