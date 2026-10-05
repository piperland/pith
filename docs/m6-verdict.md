# M6 verdict: PASS — inference slices + generic call-side machinery + spike slices, real coverage holds

Date: 2026-10-05. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M6 asked whether the engine could grow value-aware inference slices
(literal/RegExp const kinds, literal-defaulted params) plus generic call-side
machinery (ident-arg instantiation, structural admission, ambient overloads,
contextual arrows, explicit type-arg ident checks) without breaking a single
existing verdict. Every thread verified PASS independently; the suite stands
at 692 → 805 green with zero failures. Real-corpus coverage holds 1/33
EXECUTED across two re-trials (P065 at 29 notes; P071 at 26 notes — destr 8→5
EXECUTED via the P066 driver backfill, confirmed in P071).

## Per-thread basis

- P060 widened-kind inference: literal/primitive/null/undefined/regex consts silent with kind flow; array/object/non-literal byte-identical. `a485e49`. 708 pass. Differential check-const 39/39 MATCH (33 + 6 new), solver 7/7 match-or-pin per worker. No REJECT.
- P061 ident-arg generic instantiation (one level): literal/P060-inferred/ident args bind per position; unresolvable distinct declines; P036 priority intact. `2a65b0d`. 728 pass. Differential check-generics 31/31 MATCH (25 + 6 new), solver 11 pairs + 11 clean + 9 pinned per worker. Pinned divergence kept open: explicit type-args skip ident resolution (p09) — closed by P069. No REJECT.
- P062 structural admission for locally-shaped named params: member-wise via P017 comparison; imported/qualified/methoded/non-literal/generic distinct declines. `228b6fa`. 751 pass. Differential check-calls 36/36 MATCH (27 + 8 + 1 support), solver 4 matches + 4 pins per worker. No REJECT.
- P063 ambient overload admission: bodyless overload groups resolve calls via any-match; TS2391 declaration diagnostics + impl-signature participation stay declined; generic/union decls (plimit) explicitly out of scope. `6b5fc50`. 764 pass. Differential check-calls 46/46 + check-functions 82/82 MATCH, solver 7 calls + 3 divergence + 2 functions + 1 test per worker. First-pass green. No REJECT.
- P064 contextual arrow params: arrows in typed positions bind kinds from the expected signature; free-standing/returns-dependent/rest/destructured distinct declines. `3888003`. 790 pass. Differential check-calls 53/53 + check-functions 85/85 MATCH, solver 4 clean + 2 wrong-body + 4 pinned per worker. No REJECT.
- P065 M6 re-trial (doc-only): unchanged P027–P029 drivers ×3 runs, 3 passed each, 1/33 HOLDS at 29/29/29 notes. `d4661b1`. P060 destr 8→5 NOT CONFIRMED (executed 8 — driver-seam gap: real driver maps NonLiteral verbatim, RegExp silence needs the const-suite seam); P050 guard-effect reason refinement VISIBLE (jsonParseTransform complex-body → effect-call-direct); all other threads scoped no-ops confirmed.
- P066 real-driver regex backfill (test-only seam mirror): 3 regex consts EXECUTED silent, 5 identical reasons. `68cb116`. 790 pass (counts identical to P064). Destr 0 diag, 5 unsupported EXECUTED.
- P068 spike (design-only, no code): ranked slices for generics instantiation — (d) explicit type-arg ident-kind check 8/10, (b) literal-defaulted param kind flow 7/10, (a) T-slot partial admission 5/10 (prerequisite, 0 notes alone), (c) generic-alias contextual arrows 2/10 NO-GO. Accepted commit n/a. Both implementable slices built as P069/P070.
- P069 explicit type-arg ident-kind check (spike slice d): explicit branch resolves bare idents via IdentTable; unresolvable keeps skip; inferred path/priority/literal-inference untouched. `5ad798d`. 795 pass. Differential check-generics 34/34 MATCH (31 + 3 new), solver 12 pairs + 12 clean + 11 pinned (was 11/11/9 — P061 p09 divergence flipped to TS2345-at-arg). No REJECT.
- P070 literal-defaulted param kind flow (spike slice b): literal defaults source widened kinds; brace/non-literal/bare-optional byte-identical; arity unchanged. `b2995dd`. 805 pass. Differential check-functions 89/89 MATCH (85 + 4 new), solver 2 fixtures + 2 pins per worker. No REJECT.
- P071 M6 re-trial (doc-only): unchanged drivers ×3 runs, 3 passed each, 1/33 HOLDS at 26/26/26 notes (19 defu + 5 destr + 2 plimit). `4265403`. P066 destr 8→5 CONFIRMED executed 3/3; P069/P070 scoped no-ops on real files (driver feeds `ident: None`, `default_kind: None`); all other threads no-ops confirmed as in P065.

## Real-corpus walk

P065 executed the full re-trial (engine P048–P064 at `3888003`, 5/5 sha256 pins match, zero diagnostics ×3 runs, 29/29/29 notes): defu CONFIRM-silent import holds, plimit ambient overloads still decline (P063 non-generic scope), destr at 8 with `warnKeyDropped` EXECUTED silent. P066 executed the seam backfill (test-only, no solver change): destr 8→5 EXECUTED. P071 re-executed everything (engine P060–P070 at `b2995dd`, fresh box, 5/5 pins match, zero diagnostics ×3 runs, 26/26/26 notes): the 3 regex consts EXECUTED silent, remaining 5 destr notes byte-identical reasons, no other file moved. Coverage: **1/33 EXECUTED, 5/5 files EXECUTED** throughout. No other delta is claimed executed.

## Ranked M7 gaps (P071 executed note frequency, n=26; −3 vs P065, all three the now-silent regex consts)
1. Unannotated decls, no inference - 8 notes, 3 files (defu.ts x6, destr `_value` x1, _utils x1).
2. Named/generic param types (`T` x3, `Merger` x3, `Options` x1) - 7 notes, 2 files; P061 binds literal/ident args only.
3. Undeclared callback names (`merger` x1, `currentValue` x2) - 3 notes, 1 file.
4. Complex bodies (`isPlainObject`, `destr`) - 2 notes.
5. Ambient overloads without bodies (`pLimit`, `limitFunction`) - 2 notes, generic — P063 explicitly out of scope.
6. Singletons - 4 notes: effect-call-direct guard arm (`jsonParseTransform`), non-literal return (`safeDestr` spread), cross-file named return (`DefuFunction`), unannotated param (`namespace`).

These need thesis-level machinery — generics instantiation from non-literals,
named function types with operators (keyof/indexed/conditional), inference for
non-literal inits, ambient generic decls. The spike's hard line stands: stop
before type-operator evaluation (slice (c) is NO-GO — invented structure,
trips H-002). No roadmap is offered beyond that statement; any claim smaller
than that would be false.

M6 closed the loop it opened: every inference/generic shape checks per position
with oracle-pinned divergences (one honest flip: P061 p09 → P069), every
declined shape names its reason, and the real corpus says 1/33 EXECUTED — with
the one constructional miss (8→5) honestly corrected, backfilled, and
re-executed.
