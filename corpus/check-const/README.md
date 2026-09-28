# check-const corpus (PITH-P009)

First solver-thread fixtures: `const` declarations with primitive
annotations. Oracle baselines are tsc 7.0.2 via
`.agent/scripts/pith-oracle/run.mjs` (normalized `file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| annotated-correct.ts | clean | silent (5 decls, no diagnostics) |
| mismatch-number.ts | 1x TS2322 | 1x PITH2322 (message shape mirrors tsc) |
| mismatch-string.ts | 1x TS2322 | 1x PITH2322 |
| mismatch-boolean.ts | 1x TS2322 | 1x PITH2322 |
| unknown-annotation.ts | 1x TS2304 | 1x PITH2304 (message identical to tsc) |
| union-annotation.ts | clean | UNSUPPORTED (union outside subset) |
| no-annotation.ts | clean | UNSUPPORTED (inference outside subset) |
| multi-declarator.ts | 1x TS2322 | 1x PITH2322 on `third` |

Differential: 6/6 match on the primitives subset (5 silent/clean + 5
diagnostic pairs across 4 fixtures, code family + message shape); 2/2
out-of-subset recorded as UNSUPPORTED, never silent.
