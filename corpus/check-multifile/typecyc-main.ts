// Solver verdict: no diagnostics; two declines (the cyclic import plus the
// uncheckable annotation). Oracle tsc is silent here — its TS2303 errors
// land on the re-export statements instead (pinned gap).
import { Cyc } from "./typecyc-a";
const c: Cyc = 1;
