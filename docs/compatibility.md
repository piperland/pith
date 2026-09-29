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
