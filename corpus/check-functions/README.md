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
still reports); loops, `switch`, `else-if` chains, `if/else` plus a tail
return, `throw`/bare branches outside `try` arms, and `continue` still decline
(unit-pinned).

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
| straight-identifier-init.ts | 1x TS2322 | 1x PITH2322 (propagation — first flip) |
| straight-let-init-declined.ts | 1x TS2322 | silent + 1 UNSUPPORTED (`let` never propagates) |

Differential: 9/9 match-or-pin on the straight subset (8 diagnostic/silent
pairs + 1 pinned oracle-error divergence — `let` bindings need flow facts
the subset refuses). Still declining by design: `var`, destructured
bindings, deeper nesting, non-terminal returns, bodies past the four-item
cap, and every P023-era exclusion (loops, `switch`, joins-plus-tail).

## P039 try/catch bodies

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| try-clean.ts | clean (incl. clean tail) | silent, 0 notes (arms + tail per position) |
| try-try-wrong.ts | 1x TS2322 (try arm) | 1x PITH2322 |
| try-catch-wrong.ts | 1x TS2322 (catch arm) | 1x PITH2322 |
| try-both-wrong.ts | 2x TS2322 | 2x PITH2322 (arms independent) |
| try-tail-wrong.ts | 1x TS2322 (tail) | 1x PITH2322 (tail is another position) |
| try-finally-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| try-throw-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| try-binding-unused.ts | clean | silent, 0 notes (plain binding admits; `e` unused) |
| try-binding-used.ts | 1x TS2322 (`unknown`) | silent + 1 UNSUPPORTED (non-literal arm gate) |

Differential: 9/9 match-or-pin (6 diagnostic/silent pairs + 2 pinned
oracle-clean divergences — `finally` clauses and `throw` arms need
control-flow facts the subset refuses — + 1 pinned oracle-error
divergence: a used catch binding types `unknown` in tsc while the subset
has no binding value-type facts). Each arm checks independently
through the same synthetic delegation as joins (no fixpoint, single
pass). Still declining by design with distinct recorded reasons:
`finally` clauses, destructured catch patterns, and non-straight
arms or tails (multi-statement, bare returns). Probes in
`.agent/scratch/p039-probes/`.

## P040 switch bodies

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| switch-clean.ts | clean | silent, 0 notes (cases + default per position) |
| switch-case-wrong.ts | 1x TS2322 (case arm) | 1x PITH2322 |
| switch-default-wrong.ts | 1x TS2322 (default arm) | 1x PITH2322 |
| switch-two-wrong.ts | 2x TS2322 | 2x PITH2322 (cases independent) |
| switch-fallthrough-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| switch-complex-case-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |

Differential: 6/6 match-or-pin (4 diagnostic/silent pairs + 2 pinned
oracle-clean divergences — fallthrough and multi-statement cases need
control-flow facts the subset refuses). Each case plus the optional
default checks independently through the same synthetic delegation as
joins (no fixpoint, single pass). Still declining by design with
distinct recorded reasons: fallthrough, complex cases, case-level
declarations, non-literal discriminants or labels, duplicate defaults.
A missing `default` admits (tsc's `TS2366` exhaustiveness error is a
pinned gap — no corpus fixture). Probes in
`.agent/scratch/p040-probes/`.

## P041 counted-`for` bodies

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| for-clean.ts | clean | silent, 0 notes (body + tail per position) |
| for-body-wrong.ts | 1x TS2322 (loop body) | 1x PITH2322 |
| for-zero-trip.ts | 1x TS2322 (zero-trip body still reports) | 1x PITH2322 (trips unmodeled) |
| for-nonliteral-bound-declined.ts | 1x TS2322 (`i < n`) | silent + 1 UNSUPPORTED (pinned divergence) |
| for-while-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| for-complex-body-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |

Differential: 6/6 match-or-pin (3 diagnostic/silent pairs + 2 pinned
oracle-clean divergences — `while` loops and multi-statement bodies need
flow facts the subset refuses — + 1 pinned oracle-error divergence: a
non-literal bound needs value-type facts). The loop body plus the
optional tail checks independently through the same synthetic delegation
as joins (no fixpoint, single pass — loop-carried verdicts are an
explicit pinned gap). Still declining by design with distinct recorded
reasons: non-literal bounds, non-numeric bounds, non-idiom headers,
non-`for` loops, infinite `for(;;)`, `break`/`continue` bodies, complex
bodies/tails (unit-pinned). Probes in
`.agent/scratch/p041-probes/`.

## P043 throw bodies

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| throw-guard-clean.ts | clean | silent, 0 notes (guard throw emits no verdict; tail checks) |
| throw-guard-tail-wrong.ts | 1x TS2322 (tail) | 1x PITH2322 |
| throw-straight-clean.ts | clean | silent, 0 notes (mid-sequence throw skipped) |
| throw-straight-inner-wrong.ts | 1x TS2322 (inner) | 1x PITH2322 (positions independent) |
| throw-straight-tail-wrong.ts | 1x TS2322 (tail) | 1x PITH2322 (unreachable tail still checks) |
| throw-terminal-inner-wrong.ts | 1x TS2322 (inner) | 1x PITH2322 (no tail; leadings still check) |
| throw-only.ts | clean | silent, 0 notes (zero positions) |
| throw-complex-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |

Differential: 8/8 match-or-pin (7 diagnostic/silent pairs + 1 pinned
oracle-clean divergence — `if/else` with a throw branch needs flow facts
the subset refuses). `throw` accepts any value (`throw "s"` is clean), so
throw positions emit no diagnostic family and carry no facts; guard
throws (block-transparent, any condition) plus tail returns, straight
bodies with throws anywhere in the sequence, terminal throws, and lone
throws admit through the same synthetic delegation as joins (no fixpoint,
single pass). Still declining by design with distinct recorded reasons:
`throw` arms in `try`/`catch`, `throw` cases or defaults in `switch`,
throw tails after guard returns, and any other multi-path body. Probes in
`.agent/scratch/p043-probes/`.

## P045 else-if chains

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| elseif-clean.ts | clean | silent, 0 notes (branches per position) |
| elseif-branch-wrong.ts | 1x TS2322 (middle branch) | 1x PITH2322 |
| elseif-two-wrong.ts | 2x TS2322 | 2x PITH2322 (branches independent) |
| elseif-missing-else.ts | 1x TS2366 | silent + 1 UNSUPPORTED (pinned divergence) |
| elseif-nested-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| elseif-complex-branch-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |

Differential: 6/6 match-or-pin (3 diagnostic/silent pairs + 2 pinned
oracle-clean divergences — nested chains and throw branches need flow
facts the subset refuses — + 1 pinned oracle-error divergence: a missing
terminal `else` reports `TS2366` while the subset has no
declaration-completeness family). Each branch of a full
`if`/`else-if`/…/`else` chain checks independently through the same
synthetic delegation as joins (no fixpoint, single pass — any condition
qualifies, single-statement blocks unwrap). Still declining by design
with distinct recorded reasons: missing terminal `else`, nested chains,
and complex branches (unit-pinned); an `else-if` chain paired with any
other statement stays `Complex` (the P023 `if/else`-plus-tail precedent).
Probes in `.agent/scratch/p045-probes/`.

## P046 named (interface/alias) params

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| named-param-clean.ts | clean | silent, 0 notes (interface + alias + primitive params admit as opaque) |
| named-param-body-wrong.ts | 1x TS2322 (tail) | 1x PITH2322 |
| named-param-unused.ts | clean | silent, 0 notes (untouched named param; leadings + tail check) |

Differential: 3/3 match (2 silent/clean + 1 diagnostic pair). Named
params admit as opaque definition-side: the annotated gate already
accepts every annotated param, and no value-type facts about the param
flow anywhere (H-002). Body positions touching the param ride the
existing gates (`return p` declines whole-decl via the non-literal
position gate; `const y: T = p` resolves one level — primitive params
check like their annotation (P048), the rest decline per-position —
unit-pinned, never forced verdicts). Call-site
args against named params decline distinctly per site (corpus-pinned in
check-calls). Generic `T`, union, and complex param annotations decline
exactly as before. Probes in `.agent/scratch/p046-probes/`.

## P049 void-effect bodies

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| void-effect-clean.ts | clean | silent, 0 notes (lone allowlist effect; zero positions) |
| void-effect-guard-clean.ts | clean | silent, 0 notes (arm emits nothing; bare tail trivial) |
| void-effect-guard-wrong.ts | 1x TS2322 (tail) | 1x PITH2322 (tail checks normally) |
| void-effect-guard-two-calls.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| void-effect-guard-nonallowlist.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| void-effect-guard-valued-return.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |

Differential: 6/6 match-or-pin (3 diagnostic/silent pairs + 3 pinned
oracle-clean divergences — several effect calls, non-allowlist calls,
and valued arm returns need call-site and flow facts the subset
refuses). Lone allowlist effect calls (`console.warn` shapes, arity-only
— templated arguments need no literal facts) and guard arms with exactly
one allowlist effect call plus a bare `return` admit only under `void` /
`undefined` / `any` annotations (tsc checks bare arm returns against the
annotation and spells `TS2355` for return-less non-voidish bodies); the
arm emits no verdict while the tail checks through the existing literal
paths. Still declining by design with distinct recorded reasons:
non-voidish annotations, direct calls, unknown receivers/members,
exact-arity breaches, arm `throw`s, several effect calls, and valued arm
returns (unit-pinned); every other effect shape keeps `Complex`, so
`isPlainObject` and destr's main `destr` keep their exact reasons.
Probes in `.agent/scratch/p049-probes/`.

## P050 sequential guard-return chains

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| guard-chain-clean.ts | clean | silent, 0 notes (3 guards + tail per position) |
| guard-chain-wrong-guard.ts | 1x TS2322 (2nd guard) | 1x PITH2322 |
| guard-chain-wrong-tail.ts | 1x TS2322 (tail) | 1x PITH2322 |
| guard-chain-missing-tail.ts | 1x TS2366 | silent + 1 UNSUPPORTED (pinned divergence) |
| guard-chain-interleaved-declined.ts | clean | silent + 1 UNSUPPORTED (pinned divergence) |
| void-effect-guard-ident-tail.ts | 1x TS2322 (tail) | 1x PITH2322 (P048 resolution — V049 gap) |

Differential: 6/6 match-or-pin (4 diagnostic/silent pairs + 1 pinned
oracle-error divergence — guards without a tail report `TS2366` while the
subset has no declaration-completeness family — + 1 pinned oracle-clean
divergence: a `const` breaking the guard run needs flow facts the subset
refuses). N consecutive `if (c) return X;` guards (at least two — a lone
guard plus straight-line code keeps `Complex`) plus a terminal valued
`return` check independently through the same synthetic delegation as
joins (no fixpoint, single pass — any condition qualifies, the P023
precedent); complex guards and bare tails decline with distinct recorded
reasons (unit-pinned), never a partial verdict. Bare-identifier
guard-effect tails resolve one level through P048 and check like
literals (the V049 composition gap — `: void` diagnoses exactly like tsc
while `: any` stays silent). Probes in
`.agent/scratch/p050-probes/`.

## P051 ternary returns

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| ternary-return-clean.ts | clean | silent, 0 notes (arms per position) |
| ternary-return-wrong-then.ts | 1x TS2322 (then arm) | 1x PITH2322 |
| ternary-return-wrong-else.ts | 1x TS2322 (else arm) | 1x PITH2322 |
| ternary-return-both-wrong.ts | 2x TS2322 | 2x PITH2322 (arms independent) |
| ternary-return-ident.ts | 1x TS2322 (parameter arm) | 1x PITH2322 (P048 resolution) |
| ternary-return-nested-declined.ts | 1x TS2322 (inner arm) | silent + 1 UNSUPPORTED (pinned) |
| ternary-return-complex-declined.ts | 1x TS2322 (literal arm) | silent + 1 UNSUPPORTED (pinned) |
| ternary-return-any-arm.ts | 1x TS2322 (literal arm) | 1x PITH2322 (accept-all arm emits nothing) |
| ternary-return-unknown-arm.ts | 1x TS2322 (`unknown` arm) | 1x PITH2322 |
| ternary-return-never-arm.ts | 1x TS2322 (literal arm) | 1x PITH2322 (`never` arm vanishes) |

Differential: 10/10 match-or-pin (8 diagnostic/silent pairs + 2 pinned
oracle-error divergences — nested/complex arms decline whole-declaration
where the oracle still checks the checkable arm). Return arms diagnose at
arm spans through dotted synthetic names; const-position joins diagnose
once at the declaration (see the check-const P051 section). Probes in
`.agent/scratch/p051-probes/`.
