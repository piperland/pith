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
| alias-primitive-correct.ts | clean | silent (primitive aliases check like targets) |
| alias-primitive-wrong.ts | 1x TS2322 | 1x PITH2322 spelling the target |
| alias-chained-declined.ts | clean | UNSUPPORTED (single-level expansion only) |
| alias-shadowed-declined.ts | clean | UNSUPPORTED (local values shadow aliases) |
| alias-generic-declined.ts | clean | UNSUPPORTED (generic aliases never instantiate) |
| alias-interface-declined.ts | clean | UNSUPPORTED (named shapes need the enum entry) |
| ident-chain.ts | 1x TS2322 | 1x PITH2322 on `c`, silent on `b` (propagation) |
| ident-cycle-declined.ts | TS2448 + TS2454 | silent + 2 UNSUPPORTED (forward, then cycle) |
| ident-depth2-declined.ts | 1x TS2322 | silent + 1 UNSUPPORTED (single level only) |
| ident-let-declined.ts | 1x TS2322 | silent + 1 UNSUPPORTED (top-level `let` has no facts) |

Differential: 9/9 match (2 silent/clean + 7 diagnostic pairs across 7
fixtures, code family + message shape); 9/9 out-of-subset recorded as
UNSUPPORTED, never silent (6 oracle-clean + 3 pinned oracle-error
divergences — cycles, depth-2+ chains, and `let` sources).

Local aliases (PITH-P038): single-level expansion mirrors the P035
imported-alias rules — alias-to-primitive/boundary rewrites the annotation
spelling, chained/generic/circular/complex targets decline with distinct
reasons, and local consts win over alias names (never hijack a value
binding). Alias-to-interface/enum checks through the `check_enums` entry
(see `crates/pith-solver/tests/e2e_check_enums_namespaces.rs`); the
`check_file` entry used here declines those with an entry-point reason.
