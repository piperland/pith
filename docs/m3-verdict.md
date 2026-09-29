# M3 verdict: PASS (narrow) — module system boots, real files execute

Date: 2026-09-29. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M3 asked whether the M2-narrow engine could grow outward without losing
depth: module-checked imports (P022), join bodies (P023), member calls
(P024), any/casts (P025), and three executed real-file verdicts
(P026-P029). Every thread verified PASS independently; the full suite
stands at 359 green with zero failures. Real-corpus coverage moved
0/33 → 1/33 EXECUTED (not projected).

## Per-thread basis

- P022 module-checked e2e: defu-shaped 3-file case checks (PITH2322 +
  PITH2345 on main); `import type` failures decline (never false
  PITH2305/2307/2304); invalidation shared-2/leaf-1 on the checked graph.
  Two CTO-caught bugs fixed in gating (repeat-call false decline,
  double-decline on failed type-only imports). 306 pass at acceptance.
- P023 join bodies: sequence/guard-tail/branch returns check per position
  through synthetic delegation; NonLiteral positions decline whole-decl;
  branching + multi-return flipped honestly; unreachable returns still
  check (re-probed). 316 pass.
- P024 member calls: closed allowlist (JSON/Object/Array/console/Math)
  with opaque probed signatures through the shared verdict tail (P014
  behavior proven byte-identical); lib/unknown shapes decline; two pinned
  oracle-error divergences. 329 pass.
- P025 any/casts: contract premise FALSIFIED by probes (explicit `any`
  flows are silent in tsc) and the solver mirrors the oracle, disclosed;
  TS2352/TS1360 declines at operand spans with downstream checks
  preserved; complex casts + unguarded `unknown` decline. Heavy CTO
  repairs (mechanical corruption, `check_one` split, span pins).
  356 pass.
- P026 re-trial: prescan-v2 1/33 with per-case Pith wall times
  (parse+bind: defu 2ms, destr 1ms, plimit 0ms — no win claims).
- P027 defu verdict: EXECUTED CONFIRM — import binding silent, 0 diag +
  17 established-reason notes on defu.ts.
- P028 destr verdict: EXECUTED decline CONFIRMS projection (complex-body
  reason refined from the guessed bare-return).
- P029 plimit verdict: EXECUTED decline CONFIRMS projection
  (overload-signature ambient mechanism refined from guessed
  declare-form). All three real cases executed; 359 pass.

## Ranked M4 gaps (from executed evidence)

1. Bodies beyond joins (loops, switch, try, multi-statement straights) —
   blocks destr-shaped code and most real functions.
2. Generics admission (constraints, defaults, infer, multi-param) —
   blocks defu-shaped utilities and lib types.
3. `unknown` value-type facts + full `any`-boundary depth.
4. Lib/ambient type space (Promise, Iterable, overloads beyond pins).
5. Type aliases / interfaces-as-exports in the value graph.
6. Optional/default/rest parameter ranges and member-call breadth.

M3 closed the loop it opened: every M2 divergence class is now either
checked or declined with an executed reason, and the engine has
verdicts — not projections — on pinned real-world files.
