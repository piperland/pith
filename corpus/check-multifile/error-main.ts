// Solver verdict: one PITH2322 (oracle TS2322) at the declarator,
// one PITH2345 (oracle TS2345) at the mismatched argument.
import { NAME, add } from "./error-shared";
const n: number = NAME;
add(1, "oops");
