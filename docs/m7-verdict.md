# M7 verdict: PASS — spike-ranked generic slices built, suite holds 805, real coverage holds

Date: 2026-10-05. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M7 asked whether generic instantiation could advance from non-literal
positions (explicit type-arg idents, literal-defaulted params) within the
spike's H-002 hard lines, without breaking a single existing verdict. Both
implementable spike slices built and verified PASS independently (P069, P070);
the suite stands at 795 → 805 green with zero failures. Real-corpus coverage
holds 1/33 EXECUTED at 26 notes (P071 re-trial, 3/3 runs byte-identical);
P073's expected namespace conversion was FALSIFIED by execution (0-note
delta — the param is unannotated, whole-decl gate fires first). The destr
8→5 backfill stands EXECUTED.

## Per-thread basis

- P068 spike (design-only, no code): ranked generics-instantiation slices — (d) explicit type-arg ident-kind check 8/10, (b) literal-defaulted param kind flow 7/10, (a) T-slot partial admission 5/10 (prerequisite, 0 notes alone), (c) generic-alias contextual arrows 2/10 NO-GO (needs keyof/indexed/conditional — thesis breach). Accepted commit n/a. Both implementable slices built as P069/P070.
- P069 explicit type-arg ident-kind check (spike slice d): explicit branch resolves bare idents via IdentTable; unresolvable keeps skip; inferred path/priority/literal-inference untouched. `5ad798d`. 795 pass. Differential check-generics 34/34 MATCH (31 + 3 new), solver 12 pairs + 12 clean + 11 pinned (was 11/11/9 — P061 p09 divergence flipped to TS2345-at-arg). No REJECT.
- P070 literal-defaulted param kind flow (spike slice b): literal defaults source widened kinds; brace/non-literal/bare-optional byte-identical; arity unchanged. `b2995dd`. 805 pass. Differential check-functions 89/89 MATCH (85 + 4 new), solver 2 fixtures + 2 pins per worker. No REJECT.
- P071 M7 re-trial (doc-only): unchanged drivers ×3 runs, 3 passed each, 1/33 HOLDS at 26/26/26 notes (19 defu + 5 destr + 2 plimit). `4265403`. Destr 8→5 CONFIRMED executed 3/3 (3 regex consts silent, `_value` still declines); P069/P070 scoped no-ops on real files (driver feeds `ident: None`, `default_kind: None`); all other threads no-ops confirmed.
- P073 real-driver literal-default seam (test-only): mirrors the functions-driver `map_init` rule verbatim; premise FALSIFIED — `namespace` param unannotated, whole-decl gate precedes IdentTable, so P070's annotated-defaults flow never fires. `4746ec1`. 805 pass (identical counts), all real verdicts byte-identical, 0-note delta. Kept for driver consistency, zero behavior change. No REJECT.
- (P072 was the M6 verdict-doc update — part of M6, not an M7 thread; excluded here.)

## Real-corpus walk

P071 executed the full re-trial (engine P060–P070 at `b2995dd`, fresh box `ivh2pa8jcr4v7h5zyhxdz`, 5/5 sha256 pins match, zero diagnostics ×3 runs, 26/26/26 notes): defu CONFIRM-silent import holds, the 3 regex consts EXECUTED silent via the P066 seam, remaining 5 destr notes byte-identical reasons, plimit 2 notes unchanged. P073 re-executed live verdicts (box `i67u826z93ibavxavb1lb`, TEST_EXIT=0 first-pass): every file line byte-identical (defu 2/0/17, destr 5, plimit 2), `namespace` note persists by design. Coverage: **1/33 EXECUTED, 5/5 files EXECUTED** throughout. No other delta is claimed executed.

## M8 statement: the thesis wall (P071 executed note frequency, n=26)

1. Unannotated decls, no inference — 8 notes (defu.ts ×6, destr `_value` ×1, _utils ×1). Blocker: inference for non-literal inits (member calls, casts) — needs value facts the single-pass subset refuses to invent.
2. Named/generic param types — 7 notes (`T` ×3 needs generic instantiation from non-literal args; `Merger` ×3 needs generic-alias keyof + indexed access + conditional evaluation; `Options` ×1 needs shaped non-literal object facts, solver already admits).
3. Undeclared callback names — 3 notes (`merger` ×1, `currentValue` ×2). Blocker: interprocedural/user-call arms — resolving names passed through user functions.
4. Complex bodies — 2 notes (`isPlainObject`, `destr`). Blocker: control-flow analysis — explicitly out of subset.
5. Ambient generics — 2 notes (`pLimit`, `limitFunction`). Blocker: ambient generic decls with non-primitive bounds + function-typed params — triple-gated, P063 explicitly out of scope.
6. Singletons — 4 notes: effect-call-direct guard arm (`jsonParseTransform`), non-literal return (`safeDestr` spread), cross-file named return (`DefuFunction`), unannotated param (`namespace` — whole-decl gate precedes any default flow).

Each remaining note needs thesis-level machinery — the spike's hard line
stands: stop before type-operator evaluation (slice (c) is NO-GO — invented
structure, trips H-002). No roadmap is offered beyond that statement; any
claim smaller than that would be false.

M7 closed the loop it opened: both buildable spike slices check per position
with oracle-pinned divergences (one honest flip: P061 p09 → P069), one honest
falsification (P073 namespace premise), every declined shape names its reason,
and the real corpus says 1/33 EXECUTED.
