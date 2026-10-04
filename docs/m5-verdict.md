# M5 verdict: PASS — value-fact substrate with divergence flips, real coverage holds

Date: 2026-10-04. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M5 asked whether the engine could grow a value-fact substrate — identifier
literals, void effects, guard chains, ternary arms, alias chains, enum member
refs — and flip honest divergences (t3, chain pins, enum asserts) without
breaking a single existing verdict. Every thread verified PASS independently;
the suite stands at 579 → 692 green with zero failures. Real-corpus coverage
holds 1/33 BY CONSTRUCTION (no M5 re-trial executed; destr 9→8 note delta is
constructional — see below).

## Per-thread basis

- P048 ident literal propagation: single-level const chains check at use span, annotated sources flow by annotation; cycles/let/reassign/depth-2+/cross-file/unannotated distinct declines. `b365a2e`. 611 pass. Differential check-const 18/18 + check-functions 57/57 MATCH (t3 honest flip, solver const 9/9 + 3 pins per worker).
- P049 void-effect bodies: lone allowlist effect calls silent, effect-skipped guard arms check tails; all other effect shapes distinct declines. `9ac45a0`. 620 pass. Differential check-functions 63/63 MATCH (57 + 6 new), solver 6/6 match-or-pin per worker.
- P050 sequential guard-return chains: N guards + tail check per position, TS2366 missing-tail pin, nested/complex/missing-tail distinct declines; bonus GuardEffect ident-tail composition. `64ad0fb`. 631 pass. Differential check-functions 69/69 MATCH (63 + 6 new), solver 6/6 match-or-pin per worker.
- P051 ternary positions: arms check per arm (const joins diagnose once with union spelling, returns per arm); nested/complex/fresh-mix distinct declines. `aa47b4d`. 670 pass. Differential check-const 30/30 + check-functions 79/79 MATCH, solver 12 const + 10 function fixtures per worker.
- P052 transitive alias chains: bounded (8) resolution with visited-set cycles; chained-decline pins flip to matches. `40b49fb`. 681 pass. Differential check-const 33/33 + enums 9/9 + multifile 27/27 MATCH, solver 4 flips + new pins per worker.
- P053 enum member value refs: identity rule (same-enum clean, cross-enum TS2322 spelling `Enum.Member`); computed/unknown/ambient distinct declines. `b97d57f`. 692 pass. REJECT on uniform spelling → cardinality flip (singleton source → `Enum`, else `Enum.Member`) re-verified PASS. Differential check-enums-namespaces 14/14 + check-const 33/33 MATCH, solver singleton fixture + 2 flipped asserts.

## Real-corpus walk

No M5 re-trial was executed: the 1/33 EXECUTED baseline (P042, 30/30/30 notes ×3 runs) stands by construction. The single constructional delta: P049's void-effect admission makes destr's `warnKeyDropped` silent, so destr's executed note count projects 9→8 — BY CONSTRUCTION, not re-executed. This awaits the next re-trial for EXECUTED status; it is not claimed as executed here. All other files unchanged by construction: defu CONFIRM-silent import still holds (M5 admits no generic/named/inference machinery), plimit ambient overloads still decline (P053 covers member refs, not ambient decls), and the remaining destr declines still hit established reasons (complex bodies, non-literal return, unannotated consts).

## Ranked M6 gaps (P042 executed note frequency, n=30 - buckets verbatim)
1. Unannotated decls, no inference - 11 notes, 3 files (defu.ts x6, destr x4, _utils x1).
2. Named/generic param types (`T` x3, `Merger` x3, `Options` x1) - 7 notes, 2 files; P046 made named params opaque (not checkable), P048-P053 add no generic machinery.
3. Complex bodies (`isPlainObject`, `jsonParseTransform`, `warnKeyDropped`, `destr`) - 4 notes, 2 files; P049 silenced `warnKeyDropped` by construction (destr 9->8 unexecuted).
4. Undeclared callback names (`merger` x1, `currentValue` x2) - 3 notes, 1 file.
5. Ambient overloads without bodies (`pLimit`, `limitFunction`) - 2 notes, 1 file; P044 resolves calls, not ambient decls.
6. Non-literal return (`safeDestr` spread) + cross-file named return + unannotated param - 3 notes.

These need thesis-level machinery — value-aware inference, generic
instantiation, named-type checking — not incremental fixtures. No roadmap is
offered beyond that statement: M6 is inference-and-generics territory, and any
claim smaller than that would be false.

M5 closed the loop it opened: every value-fact shape checks per position with
oracle-pinned divergences, every declined shape names its reason, and the
real corpus projection says so by construction — with the one delta honestly
marked unexecuted.
