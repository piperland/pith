# M2 verdict: PARTIAL (strong-narrow)

Date: 2026-09-29. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).

## Verdict logic

M2 required depth (honest differentials per thread) plus a breadth signal
(real files checking end-to-end). Depth met. Breadth failed by design.

- All threads P010-P020 verified PASS independently, gates green
  (fmt, clippy `--workspace --all-targets -- -D warnings`, workspace tests).
  Cumulative: 301 tests green at P021 (`52+1+2+7+100+10+21+10+11+10+12+10+18+10+10+11+6`).
- Real trial (P021): 3 cases clean under tsc, Pith parse+bind clean with zero
  panics (`corpus_smoke`), but strict subset coverage 0/33 (0%).
  Every decline cites an established, unit-pinned reason.

## Per-thread basis

- Consts (P009-P011): 6/6 match + 2 unsupported; e2e 10/10, zero hand-feed.
- Objects (P012): 8/8 match; freshness-gated excess; scope-index bug fixed.
- Functions (P013): 6/6 + 2 pinned (TS7006 param, TS2322 branch).
- Calls (P014): 5/5 + 3 pinned (unresolved/overload/rest).
- Narrowing (P015): 5 refine + 3 decline; first-line union fold.
- Generics (P016): 2/2 pairs + 8 pinned; shape-vs-calls separation fixed.
- Interfaces (P017): 4 error baselines (name-spelled) + 4 clean declines.
- Enums/namespaces (P018): 8/8; TS2694/2709/2749/2713 mirrors.
- Multifile (P019): 5/5 cases; PITH2305/2307 mirrors; leaf 1/4, shared 2/4
  invalidation through the real `QueryDb` path.
- Classes (P020): 4/4 + 4 pinned (methods/heritage/accessors/abstract).
- Real trial (P021): 5 pinned files, byte-verified; `pith_ms` null (stated).

## Ranked M3 gaps

1. Module `import/export` checking (26/33) — blocks any real file e2e.
2. Generics admission (~17): constraints, defaults, infer, conditionals.
3. Non-straight-line bodies: multi-return merge, loops, switch, try.
4. `any`/`unknown` boundary + `as` casts (~10).
5. Member/method calls and value property access (8).
6. Advanced types, optional/default/rest, lib/ambient types, expr-level rest.

Fixing (1) alone lifts coverage from 0% to nonzero; (1)+(3)+(5) is needed
for the first genuine diagnostic on defu/destr.
