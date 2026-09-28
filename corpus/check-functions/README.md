# check-functions corpus (PITH-P013)

Function declarations with annotated params + return type: the return
literal is checked against the return annotation (primitive/object
machinery reused). Oracle baselines are tsc 7.0.2 via
`.agent/scripts/pith-oracle/run.mjs` (normalized `file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| annotated-correct.ts | clean | silent (2 decls, incl. `export function`) |
| return-mismatch.ts | 1x TS2322 | 1x PITH2322 (message shape mirrors tsc) |
| unannotated-param.ts | 1x TS7006 | UNSUPPORTED (implicit-any inference out of subset) |
| unannotated-return.ts | clean (inferred) | UNSUPPORTED (inference out of subset) |
| multi-return.ts | clean | UNSUPPORTED (two returns, straight-line but not single) |
| branching.ts | 1x TS2322 (else branch) | UNSUPPORTED (flow phase gap, pinned) |
| object-return.ts | clean | silent (object machinery reused, member facts fact-fed) |
| excluded-shapes.ts | clean | silent, zero function facts (arrows, expressions, methods) |

Differential: 6/6 match on the straight-line subset (3 silent/clean +
2 diagnostic pairs + 1 unsupported/clean); 2/2 divergences pinned
explicitly (oracle errors, solver silent + 1 UNSUPPORTED each) — the
implicit-any rule and the flow phase are acknowledged non-goals, never
silent gaps.

Out of scope (no facts, solver never sees them): function expressions,
arrow functions, object/class methods, accessors, constructors,
anonymous default exports. `declare function`/overloads/empty bodies
decline with distinct reasons (unit-pinned; no corpus fixture).
`void` returns excluded: tsc accepts `undefined` for `void` while the
shared annotation map distinguishes them (pre-existing const-subset gap).
Call-site arity checking is FUTURE (needs call facts).
