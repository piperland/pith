# check-narrowing corpus (PITH-P015)

First flow-analysis fixtures: `typeof` guards refining union-annotated
`const`s. Oracle baselines are tsc 7.0.2 via
`.agent/scripts/pith-oracle/run.mjs` (normalized `file:TSNNNN: message`,
continuation lines kept verbatim).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| guarded-match.ts | clean | silent diagnostics (1 UNSUPPORTED: no initializer) |
| guarded-mismatch.ts | 1x TS2322 | 1x PITH2322 in the guarded region |
| unguarded-mismatch.ts | 1x TS2322 + elaboration | 1x PITH2322 over the full union (first line only) |
| else-branch.ts | 1x TS2322 | 1x PITH2322 in the else region |
| early-return.ts | 1x TS2322 | 1x PITH2322 after the guard |
| complex-guard.ts | 1x TS2322 + elaboration | UNSUPPORTED (declined, never diagnosed) |
| nested-guard.ts | clean (`never`) | UNSUPPORTED (declined, never silent-dropped) |
| nontypeof-guard.ts | 1x TS2322 | UNSUPPORTED (declined, never diagnosed) |

Differential: 5/5 refine fixtures match on (code family, first-line
message); 3/3 decline fixtures are silent with recorded reasons. The
elaboration continuation lines tsc appends to union-actual diagnostics
(`  Type 'string' is not assignable …`) are oracle-only detail: the e2e
folds them away and compares first lines (documented in
`e2e_check_narrowing.rs`).
