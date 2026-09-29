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
| multi-return.ts | clean | silent (two sequential returns, both clean) |
| branching.ts | 1x TS2322 (else branch) | 1x PITH2322 (branch join, per-return) |
| guard-return.ts | 1x TS2322 (tail return) | 1x PITH2322 (guard join, per-return) |
| two-returns.ts | 2x TS2322 (both returns) | 2x PITH2322 (sequence join, per-return) |
| object-return.ts | clean | silent (object machinery reused, member facts fact-fed) |
| excluded-shapes.ts | clean | silent, zero function facts (arrows, expressions, methods) |

Differential: 9/9 match on the straight-line-plus-joins subset (4 silent/clean +
4 diagnostic pairs incl. the double-diagnostic join + 1 unsupported/clean); 1/1
divergence pinned explicitly (oracle errors, solver silent + 1 UNSUPPORTED) —
the implicit-any rule is an acknowledged non-goal, never a silent gap.
Unreachable returns still check (probed tsc 7.0.2: a wrong unreachable return
still reports); loops, `switch`, `try`, `else-if` chains, `if/else` plus a tail
return, `throw`/bare branches, and `continue` still decline (unit-pinned).

Out of scope (no facts, solver never sees them): function expressions,
arrow functions, object/class methods, accessors, constructors,
anonymous default exports. `declare function`/overloads/empty bodies
decline with distinct reasons (unit-pinned; no corpus fixture).
`void` returns excluded: tsc accepts `undefined` for `void` while the
shared annotation map distinguishes them (pre-existing const-subset gap).
Call-site arity checking is FUTURE (needs call facts).

## P031 straight bodies (first cut)

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| straight-clean.ts | clean | silent (incl. unannotated-skip, `let`, nested-`function` shapes) |
| straight-inner-wrong.ts | 3x TS2322 (incl. multi-declarator) | 3x PITH2322, per declarator |
| straight-tail-wrong.ts | 1x TS2322 | 1x PITH2322 |
| straight-both-wrong.ts | 2x TS2322 | 2x PITH2322 (positions independent) |
| straight-nested-block.ts | 1x TS2322 | 1x PITH2322 (blocks flattened) |
| straight-object-inner.ts | 1x TS2322 | 1x PITH2322 (object path) |
| straight-unannotated-cast.ts | 1x TS2352 | 1x PITH2352 (operand span) |
| straight-identifier-init.ts | 1x TS2322 | silent + 1 UNSUPPORTED (pinned divergence) |

Differential: 8/8 match-or-pin on the straight subset (7 diagnostic/silent
pairs + 1 pinned oracle-error divergence — identifier initializers need
value-type facts). Still declining by design: `var`, destructured
bindings, deeper nesting, non-terminal returns, bodies past the four-item
cap, and every P023-era exclusion (loops, `switch`, `try`, joins-plus-tail).
