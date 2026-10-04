# M4 verdict: PASS — breadth without depth loss, real coverage holds

Date: 2026-10-04. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M4 asked whether the engine could absorb thirteen breadth primitives — lib
types, exports, generics, params, aliases, five body shapes, overloads,
branches — without breaking a single existing verdict. Every thread
verified PASS independently; the suite stands at 419 → 579 green with zero
failures. Real-corpus coverage holds 1/33 EXECUTED (no flip either way).

## Per-thread basis

- P034 lib types: Array<T>/T[] member-wise + Promise<T> async-unwrap; tuples/readonly/utils/collections/iterables distinct declines. `971f9d1`. 419 pass. Differential 8/8 MATCH (4 match + 4 pinned).
- P035 type exports: re-exported interfaces check, primitive aliases rewrite; chains/generics/circular/star distinct declines. `a993090`. 430 pass. Differential 27/27 MATCH (9 match + pinned rest).
- P036 multi-param generics: per-position inference, explicit lists, TS2558>TS2554>TS2304>TS2344>TS2345 priority. `514bd8d`. 456 pass. REJECT on evidence arithmetic only (459 vs 456), flipped per stated condition, no code touched. Differential 25/25 MATCH (9 pairs + 8 clean + 8 pinned).
- P037 optional/default/rest params + optional members: range arity incl. PITH2555, rest-prefix checks, absent-silent/present-checked. `872180b`. 471 pass. Differential calls 20/20 + object 10/10 + interfaces 8/8 MATCH.
- P038 local aliases: single-level expansion with underlying display; chained/generic/circular/complex/duplicate/shadowed distinct declines. `8d0138e`. 496 pass. Differential check-const 14/14 MATCH.
- P039 try/catch: straight try+catch arms per position + optional tail; finally/throw/non-straight/destructured-binding distinct declines. `374d177`. 513 pass. REJECT on unused bindings → flip F1-F3 admitted unused bindings structurally (used bindings decline via the non-literal arm gate). Differential 27/27 MATCH (7 match + 1 pinned divergence).
- P040 switch: literal/single-return cases + default per position; fallthrough/complex/decl/non-literal/dup-default distinct declines. `c26d362`. 524 pass. Differential 33/33 MATCH (4 match + 2 clean-pins per worker).
- P041 counted for-loops: literal-bound numeric single-pass per position; while/do/infinite/break-continue/complex distinct declines. `de621c7`. 539 pass. CTO-caught infinite-gate order bug fixed. Differential 39/39 MATCH (3 pairs + 2 clean + 1 error-pin per worker).
- P042 re-trial (doc-only, `af4da2b`): all 5 files executed, 1/33 HOLDS, ranked gaps recorded (see below). No solver changes.
- P043 throw positions: guard-throw+tail and straight-with-throw check surroundings, throw emits no family. `11b7615`. 549 pass. Differential 47/47 MATCH (7 fixtures + 1 decline per worker).
- P044 overloads: any-match resolution, impl never participates, TS2769/TS2345/TS2554/TS2555/TS2575 priority, generics excluded. `efacb4b`. 560 pass. Differential check-calls 25/25 MATCH (16/16 + 3 pins per worker; plimit not attempted).
- P045 else-if chains: full-chain per-position checks, missing-else TS2366 pin, nested/complex distinct declines. `1808c43`. 567 pass. Differential 53/53 MATCH (6/6 match-or-pin per worker).
- P046 named params: opaque admission at definition, call-side opaque decline before arity, T/union/qualified keep legacy reasons. `e0880e9`. 579 pass. Differential functions 56/56 + calls 27/27 MATCH (3/3 + 5/5 pinned per worker).

## Real-corpus walk

P042 re-ran all 5 files through the unchanged P027–P029 drivers at `de621c7` (3 runs, EXIT=0, zero diag everywhere, 30/30/30 note lines): defu CONFIRM-silent import (1/33 holds), destr decline-confirmed, plimit decline-confirmed. v3 refinements from M4 machinery (declines stand): defu `createDefu` arity → named-type `Merger` notes (P037 ranges admit), destr options note now names `Options` (P037). P043–P046 converted throw-silent, overload any-match, else-if, and named-opaque machinery, but none flips the 32 declines: `Merger` x3 stays opaque-declined (P046 by design), ambient overloads have no bodies to resolve (P044 out of scope), destr's switch+try body stays complex. Still blocked: the 5 files above with identical verdicts.

## Ranked M5 gaps (P042 executed note frequency, n=30)

1. Unannotated decls, no inference — 11 notes, 3 files.
2. Named/generic param types (`T` x3, `Merger` x3, `Options` x1) — 7 notes, 2 files; P046 made them opaque, not checkable.
3. Complex bodies (`isPlainObject`, `jsonParseTransform`, `warnKeyDropped`, `destr`) — 4 notes, 2 files.
4. Undeclared callback names (`merger` x1, `currentValue` x2) — 3 notes, 1 file.
5. Ambient overloads without bodies (`pLimit`, `limitFunction`) — 2 notes, 1 file; P044 resolves calls, not ambient decls.
6. Non-literal return (`safeDestr` spread) + cross-file named return + unannotated param — 3 notes.

M4 closed the loop it opened: every admitted shape checks per position with
oracle-pinned divergences, every declined shape names its reason, and the
real corpus says so by execution — not projection.
