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
| alias-chained-declined.ts | clean | silent (P052: chains resolve transitively to the terminal spelling) |
| alias-chain-deep.ts | 1x TS2322 | 1x PITH2322 spelling the terminal primitive (five-link chain) |
| alias-chain-mutual-declined.ts | 2x TS2456 (at the alias declarations) | silent + 1 UNSUPPORTED (pinned oracle-error divergence: no declaration diagnostics) |
| alias-chain-over-depth-declined.ts | 1x TS2322 | silent + 2 UNSUPPORTED, one per use (pinned divergence by design: nine links exceed the eight-link bound; tsc has no limit) |
| alias-shadowed-declined.ts | clean | UNSUPPORTED (local values shadow aliases) |
| alias-generic-declined.ts | clean | UNSUPPORTED (generic aliases never instantiate) |
| alias-interface-declined.ts | clean | UNSUPPORTED (named shapes need the enum entry) |
| ident-chain.ts | 1x TS2322 | 1x PITH2322 on `c`, silent on `b` (propagation) |
| ident-cycle-declined.ts | TS2448 + TS2454 | silent + 2 UNSUPPORTED (forward, then cycle) |
| ident-depth2-declined.ts | 1x TS2322 | silent + 1 UNSUPPORTED (single level only) |
| ident-let-declined.ts | 1x TS2322 | silent + 1 UNSUPPORTED (top-level `let` has no facts) |

Differential: 11/11 match (3 silent/clean + 8 diagnostic pairs across 8
fixtures, code family + message shape); 10/10 out-of-subset recorded as
UNSUPPORTED, never silent (5 oracle-clean + 5 pinned oracle-error
divergences — ident cycles, depth-2+ ident chains, `let` sources, mutual
alias cycles, and over-depth alias chains).

Local aliases (PITH-P038, chains via PITH-P052): transitive expansion mirrors
the P035 imported-alias rules — alias-to-primitive/boundary rewrites the
annotation spelling, chains resolve up to the shared depth bound (cycles and
over-deep chains decline with distinct reasons),
generic/circular/complex targets decline with distinct reasons, and local
consts win over alias names (never hijack a value binding). Alias-to-interface/enum checks through the `check_enums` entry
(see `crates/pith-solver/tests/e2e_check_enums_namespaces.rs`); the
`check_file` entry used here declines those with an entry-point reason.

## P051 ternary initializers

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| ternary-clean.ts | clean | silent (both literal arms check) |
| ternary-wrong-then.ts | 1x TS2322 (`string \| number`) | 1x PITH2322 (join spells once) |
| ternary-wrong-else.ts | 1x TS2322 (`string \| number`) | 1x PITH2322 (order never surfaces) |
| ternary-both-wrong.ts | 1x TS2322 (`string`) | 1x PITH2322 (dedup to one name) |
| ternary-ident-clean.ts | clean | silent (identifier arms resolve, then check) |
| ternary-ident-agree-wrong.ts | 1x TS2322 (`number`) | 1x PITH2322 (agree path) |
| ternary-nested-declined.ts | 1x TS2322 | silent + 1 UNSUPPORTED (pinned divergence) |
| ternary-complex-arm-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| ternary-fresh-mix-declined.ts | 1x TS2322 (fresh `number \| "ok"`) | silent + 1 UNSUPPORTED (pinned divergence) |
| ternary-any-arm-clean.ts | clean | silent (`any` absorbs the union) |
| ternary-unknown-arm.ts | 1x TS2322 (`unknown`) | 1x PITH2322 (`unknown` absorbs the spelling) |
| ternary-call-cond.ts | 1x TS2322 (`string \| number`) | 1x PITH2322 (conditions never narrow) |

Differential: 12/12 match-or-pin (9 diagnostic/silent pairs + 3 pinned
divergences — 2 oracle-error where the oracle still checks nested/fresh
shapes the subset refuses to spell, 1 oracle-clean where a call arm needs
expression facts). Union elaboration detail lines are stripped from
baselines: the differential compares diagnostic headers (the solver's
message contract is first-line, like every existing fixture). Probes in
`.agent/scratch/p051-probes/`.
