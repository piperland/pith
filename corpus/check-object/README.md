# check-object corpus (PITH-P012)

Object-literal initializers checked against object annotations, plus `let`
declarators. Oracle baselines are tsc 7.0.2 via
`.agent/scripts/pith-oracle/run.mjs` (normalized `file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| object-correct.ts | clean | silent (const + `let`, all shapes match) |
| object-missing-member.ts | 1x TS2741 | 1x PITH2741 |
| object-missing-many.ts | 1x TS2739 | 1x PITH2739 |
| object-wrong-member.ts | 4x TS2322 | 4x PITH2322 (const + `let` + both cross-shapes) |
| object-excess-member.ts | 1x TS2353 | 1x PITH2353 (fresh literal, per-occurrence table) |
| object-error-priority.ts | 1x TS2322 + 1x TS2353 | same (wrong beats excess; excess beats missing) |
| object-out-of-subset.ts | clean | 4x UNSUPPORTED (union member, 2x no annotation, non-literal init) |
| object-nested-annotation.ts | clean | 2x UNSUPPORTED (nested member type, optional member) |

Differential: 8/8 match on (code-family, message) multisets; out-of-subset
recorded as UNSUPPORTED with reasons, never silent, never forced.

Probed tsc rules pinned here: literal-order actual-type spellings with
fresh booleans literal (`{ secure: false; host: string; }`); annotation
order for expected types and missing lists; one error family per
declaration (wrong > excess > missing); excess fires only for fresh
literals (stale/aliased inits decline in the solver with the freshness
reason); `{}` targets skip excess checks (declined as unsupported).
