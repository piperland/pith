# `corpus/real` — M2 capstone real-project trial (PITH-P021)

Pinned real TypeScript files + oracle baselines + strict subset pre-scan.
Fixture conventions follow `corpus/check-*/README.md` (oracle baselines are
tsc 7.0.2 via the shared normalization).

## Layout

| Path | What |
|---|---|
| `defu/src/{defu,_utils,types}.ts` | unjs/defu v6.1.7 case (entry: `defu.ts`) |
| `destr/src/index.ts` | unjs/destr v2.0.5 case (entry: `index.ts`) |
| `plimit-stress/index.d.ts` | p-limit v7.3.3 stress case (entry itself) |
| `<case>/tsc.baseline.txt` | Normalized oracle baseline (`file:TSNNNN: msg`, empty = clean) |
| `SOURCES.md` | Provenance: URL + tag + commit + license + sha256 per file |
| `coverage-prescan.md` | STRICT per-construct in/out/unknown table (hand-authored) |
| `timings.json` | tsc wall ms per case; `pith_ms: null` (Rust runs remotely) |
| `results-template.md` | GENERATED headline table; Pith columns FILLED 2026-09-29 (parse+bind verdicts from remote runs) |

## Commands

```sh
node .agent/scripts/pith-corpus/run.mjs --record  # oracle baselines + timings + template
node .agent/scripts/pith-corpus/run.mjs           # compare; exit 1 on MISMATCH
```

## Split (honest measurement, no fabrication)

Local deliverable = oracle baselines + timings + pre-scan. The Pith pipeline
cannot execute locally (no cargo/rustc; see `.agent/scripts/REMOTE.md`), so
`results-template.md` Pith columns were filled by the CTO from remote E2B
runs against these exact pinned files (parse+bind verdicts + unsupported
classification — no checking verdicts invented). No compatibility claim
beyond baselines + pre-scan + executed pipeline silence.
