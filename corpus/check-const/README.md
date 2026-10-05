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
| no-annotation.ts | clean | silent (P060: the unannotated literal kind infers) |
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

## P060 widened-kind inference for unannotated consts
| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| no-annotation.ts | clean | silent (P060 flip: the literal kind infers) |
| unannotated-null-undefined-silent.ts | clean | silent (`null`/`undefined` infer) |
| unannotated-regex-silent.ts | clean | silent (`RegExp` infers) |
| regex-mismatch.ts | 2x TS2322 (`RegExp`) | 2x PITH2322 (mismatches spell `RegExp`) |
| regex-annotation-declined.ts | clean + 1x TS2322 | 2 UNSUPPORTED (`: RegExp` lib-declined, pinned) |
| unannotated-array-declined.ts | clean | 1 UNSUPPORTED (pinned oracle-clean divergence: no shape inference) |
| unannotated-object-declined.ts | clean | 1 UNSUPPORTED (pinned oracle-clean divergence: no shape inference) |

Differential: 7/7 match-or-pin (4 silent/diagnostic pairs + 3 pinned
divergences — 2 oracle-clean where unannotated shapes keep the historical
decline, 1 oracle-error where the oracle checks a `: RegExp` mismatch the
subset refuses to spell). Only unannotated-literal pins flip (the
`no-annotation` fixture, three unit asserts — two P048 source notes plus
the merged-pair delegation note — one converted out-of-subset shape, and
one interfaces-differential count);
unannotated `let`/array/object/call/spread/index/destructured verdicts stay
byte-identical. Probes in `.agent/scratch/p060-probes/`.

## P076 pure known-method call results

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| call-global-clean.ts | clean | silent (globals classify to probed kinds) |
| call-global-wrong.ts | 4x TS2322 | 4x PITH2322 (same spellings) |
| call-any-clean.ts | clean | silent (`any` absorbs every annotation) |
| call-any-unann.ts | clean | silent (unannotated `any` absorbs via P025) |
| call-string-method-clean.ts | clean | silent (string receivers read the table) |
| call-split-clean.ts | clean | silent (`split`/`keys` spell `string[]`) |
| call-split-wrong.ts | 3x TS2322 | 3x PITH2322 (header lines; the oracle's `number[]` elaboration is stripped by the differential, like ternary unions) |
| call-anyrecv-clean.ts | clean | silent (`any` receivers absorb every method) |
| call-unlisted-declined.ts | 2x TS2339 + 1x TS2304 | silent + 3 UNSUPPORTED (pinned oracle-error divergence: no member-miss family) |
| shadowed-global-declined.ts | 1x TS2339 | silent + 1 UNSUPPORTED (pinned oracle-error divergence: shadowing bindings keep their own class, never the known-global pairs) |
| call-unann-declined.ts | clean | silent + 2 UNSUPPORTED (pinned oracle-clean divergence: the narrowed P060 exclusion stands for non-`any` calls) |
| call-never-any.ts | 1x TS2322 (`any`) | 1x PITH2322 (`any` diagnoses against `never`) |
| call-propagate.ts | 1x TS2322 | 1x PITH2322 + 1 UNSUPPORTED (the static result feeds the use while the unannotated intermediate keeps its decline) |

Differential: 13/13 match-or-pin (9 diagnostic/silent pairs + 1
elaboration-strip + 3 pinned divergences — 2 oracle-error where the oracle
spells member-miss/unknown-name errors the subset never forces (one a
shadowing receiver that keeps its own class), 1
oracle-clean where unannotated non-`any` calls keep the historical
decline). Argument arity/type errors never surface (kinds ignore args —
probed stable, pinned). Probes in `.agent/scratch/p076-probes/`.
