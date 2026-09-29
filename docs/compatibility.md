# Compatibility

Authoritative oracle: current TypeScript behavior (native `tsc`/`tsgo`).

- `docs/compatibility.md` (this file): what is supported vs not.
- Differential harness compares diagnostic code/file/start/length/message,
  inferred types, symbol and module resolution.

## Supported

- (nothing yet — PITH-P001 identity layer only)

## Known unsupported

- Everything else (see roadmap).

## Real-project corpus trial (PITH-P021 — FILLED 2026-09-29)

First honest measurement of the subset against pinned real code: 5 files /
3 cases (unjs/defu v6.1.7, unjs/destr v2.0.5, p-limit v7.3.3 `.d.ts` stress).
Provenance: `corpus/real/SOURCES.md`. Runner:
`node .agent/scripts/pith-corpus/run.mjs [--record]`.

| Case | Entry | tsc 7.0.2 baseline | tsc wall ms | Pith verdict |
|---|---|---|---|---|
| defu | `corpus/real/defu/src/defu.ts` | clean | 346 | silent (parse+bind clean; checking not driven — out-of-subset) |
| destr | `corpus/real/destr/src/index.ts` | clean | 357 | silent (parse+bind clean; checking not driven — out-of-subset) |
| plimit-stress | `corpus/real/plimit-stress/index.d.ts` | clean | 331 | silent (parse+bind clean; checking not driven — out-of-subset) |

- Strict subset coverage (hand pre-scan, `corpus/real/coverage-prescan.md`):
  **0/33 top-level constructs in-subset (0%)**, 0 unknown. Every decline
  cites an established, unit-pinned reason (module system 26/33, generics
  ~17/33, non-straight-line bodies, `any`/casts, member calls, advanced
  types, optional/default/rest, lib types).
- Robustness gate: the Rust pipeline parses and binds all 5 files with zero
  panics and dense scope indices (`corpus_smoke` test, remote E2B run;
  exact fact counts pinned). No checking verdicts are claimed: with 0%
  in-subset coverage there is nothing the checker could honestly verdict.
- M3 signal (not a promise): the top gap is the module system — without
  `import`/`export` handling no real file checks end-to-end; next are
  generics admission and multi-return/loop bodies. Narrowing fragments
  (`typeof x !== "string"` early-returns) already match subset shapes
  inside declined bodies.

## M3 cap re-trial (PITH-P026 — 2026-09-29)

Re-ran the pinned corpus through the grown pipeline; honest delta vs the
0/33 P021 baseline above. Evidence: `corpus/real/coverage-prescan-v2.md`
(full 33-construct re-score), `corpus/real/timings.json` (tsc medians of 3
local runs; per-case `pith_ms` measured remotely (top-level stays null historically)), oracle re-run 3/3 MATCH still clean.

- Strict subset coverage v2: **1/33 top-level constructs in-subset (3%)**,
  0 unknown — delta **+1**: defu's `import { isPlainObject } from
  "./_utils"` now resolves silent through the P022 checked value-import
  graph (the P019 clean-main / P022 checked-utils precedent). It is the
  only construct the pipeline would verdict today.
- Everything else confirmed out: `import type` / type re-exports decline
  by the P022 type-policy (not verdicts); all six function bodies miss the
  three P023 joins (bare returns, loops, switch, try, 3+ returns);
  `Array.isArray`/`Object.keys` verdict shapes (P024) and `any`/`as`
  admissions (P025) fire only inside already-declined bodies; generics,
  aliases, conditionals, default exports, ambient/lib types untouched.
- No Pith checking verdicts are claimed: the checker was never driven on
  these files (no driver; parse+bind evidence is the P021 remote run,
  restated). The v2 1/33 is a projection for remote confirmation, and
  `corpus_smoke` pins were left untouched — static analysis of the M3
  frontend diffs (member/cast/join facts all land in uncounted vecs or
  ride on existing facts; exactly one `functions.push` per named decl)
  shows no count drift, pending the CTO's remote verification run.
