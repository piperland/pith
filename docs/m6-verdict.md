# M6 verdict: PASS — value-aware inference slices + generic call-side machinery, real coverage holds

Date: 2026-10-05. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M6 asked whether the engine could grow value-aware inference slices
(literal/RegExp const kinds) plus generic call-side machinery (ident-arg
instantiation, structural admission, ambient overloads, contextual arrows)
without breaking a single existing verdict. Every thread verified PASS
independently; the suite stands at 692 → 790 green with zero failures.
Real-corpus coverage holds 1/33 EXECUTED (P065 re-trial at 29 notes;
P066 driver backfill executes destr 8→5, total 26 — see below).
All other deltas by construction marked unexecuted (scoped no-ops confirmed).

## Per-thread basis

- P060 widened-kind inference: literal/primitive/null/undefined/regex consts silent with kind flow; array/object/non-literal byte-identical. `a485e49`. 708 pass. Differential check-const 39/39 MATCH (33 + 6 new), solver 7/7 match-or-pin per worker. No REJECT.
- P061 ident-arg generic instantiation (one level): literal/P060-inferred/ident args bind per position; unresolvable distinct declines; P036 priority intact. `2a65b0d`. 728 pass. Differential check-generics 31/31 MATCH (25 + 6 new), solver 11 pairs + 11 clean + 9 pinned per worker. No REJECT.
- P062 structural admission for locally-shaped named params: member-wise via P017 comparison; imported/qualified/methoded/non-literal/generic distinct declines. `228b6fa`. 751 pass. Differential check-calls 36/36 MATCH (27 + 8 + 1 support), solver 4 matches + 4 pins per worker. No REJECT.
- P063 ambient overload admission: bodyless overload groups resolve calls via any-match; TS2391 declaration diagnostics + impl-signature participation stay declined; generic/union decls (plimit) explicitly out of scope. `6b5fc50`. 764 pass. Differential check-calls 46/46 + check-functions 82/82 MATCH, solver 7 calls + 3 divergence + 2 functions + 1 test per worker. First-pass green, no repairs. No REJECT.
- P064 contextual arrow params: arrows in typed positions bind kinds from the expected signature; free-standing/returns-dependent/rest/destructured distinct declines. `3888003`. 790 pass. Differential check-calls 53/53 + check-functions 85/85 MATCH, solver 4 clean + 2 wrong-body + 4 pinned per worker. No REJECT.
- P065 M6 re-trial (doc-only): unchanged P027–P029 drivers ×3 runs, 3 passed each, 1/33 HOLDS at 29/29/29 notes. `d4661b1`. P060 destr 8→5 NOT CONFIRMED (executed 8 — driver-seam gap, real driver maps NonLiteral verbatim while RegExp silence needs the const-suite seam); P050 guard-effect reason refinement VISIBLE (jsonParseTransform complex-body → effect-call-direct); all other threads scoped no-ops confirmed.
- P066 real-driver regex backfill (test-only seam mirror): 3 regex consts EXECUTED silent, 5 identical reasons. `68cb116`. 790 pass (counts identical to P064). Destr 0 diag, 5 unsupported EXECUTED.

## Real-corpus walk

P065 executed the full re-trial (engine P048–P064 at `3888003`, 5/5 sha256 pins match, zero diagnostics all files ×3 runs, 29/29/29 notes): defu CONFIRM-silent import still holds (M6 admits no generic `T`/`Merger` instantiation from non-literal positions), plimit ambient overloads still decline (P063 scopes to non-generic only), destr at 8 with `warnKeyDropped` EXECUTED silent (P049 confirmed) and `jsonParseTransform` reason refined by P050/P064 machinery. P066 executed the seam backfill (test-only, no solver change): destr 8→5 EXECUTED, remaining 5 notes byte-identical reasons. Coverage: **1/33 EXECUTED, 5/5 files EXECUTED** (26 notes post-P066). No other delta is claimed executed.

## Ranked M7 gaps (P065 executed note frequency, n=29 — buckets verbatim, P066-corrected)
1. Unannotated decls, no inference - 11 notes, 3 files (defu.ts x6, destr x4, _utils x1); 3 of 11 (destr regex) now EXECUTED silent via P066 seam backfill, remaining 8 need real inference for non-literal inits.
2. Named/generic param types (`T` x3, `Merger` x3, `Options` x1) - 7 notes, 2 files; P061 binds literal/ident args only — generic instantiation from non-literal positions unbuilt.
3. Undeclared callback names (`merger` x1, `currentValue` x2) - 3 notes, 1 file; P064 feeds `arg_arrow: None` on the real driver — scoped no-op.
4. Complex bodies (`isPlainObject`, `destr`) - 2 notes; effect-call-direct guard arm (`jsonParseTransform`) now classified separately.
5. Ambient overloads without bodies (`pLimit`, `limitFunction`) - 2 notes, generic — P063 explicitly out of scope; ambient generic decls unbuilt.
6. Singletons - 4 notes: effect-call-direct, non-literal return (`safeDestr` spread), cross-file named return (`DefuFunction`), unannotated param (`namespace`).

The Merger finding: `Merger` (generic + keyof + indexed access + conditional types) is thesis territory — beyond incremental scope, and the M7 justification. No roadmap is offered beyond that statement: M7 is generic-instantiation-from-non-literals, named generic function types, inference for non-literal inits, and ambient generic decls. Any claim smaller than that would be false.

M6 closed the loop it opened: every inference/generic shape checks per position with oracle-pinned divergences, every declined shape names its reason, and the real corpus says 1/33 EXECUTED — with the one constructional miss (8→5) honestly corrected then executed.
