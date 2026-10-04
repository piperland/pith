# check-enums-namespaces corpus (PITH-P018)

Enum-annotated consts checked against enum member facts, plus
namespace-qualified annotations resolved through binder scopes. Oracle
baselines are tsc 7.0.2 via `.agent/scripts/pith-oracle/run.mjs`
(normalized `file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| enum-numeric.ts | 4x TS2322 | 4x PITH2322 (value-membership: `5`, `2.5`, `9`, `true`) |
| enum-string.ts | 5x TS2322 | 5x PITH2322 (string literals never match; `undefined`/`null` widen) + 1x UNSUPPORTED (member access) |
| enum-const.ts | 1x TS2322 | 1x PITH2322 + 1x UNSUPPORTED (`const enum` identical, never forked) |
| enum-computed-declined.ts | clean | 3x UNSUPPORTED (computed member `A`; tsc folds `10`) |
| enum-ambient-declined.ts | clean | 2x UNSUPPORTED (`declare enum` accepts everything in tsc) |
| ns-enum.ts | 1x TS2322 | 1x PITH2322 (short name `Dir`) + 2x UNSUPPORTED (member access, qualified value) |
| ns-interface.ts | TS2741 + TS2353 + TS2322 | same families spelling `Point` + 1x UNSUPPORTED (qualified value) |
| ns-missing.ts | 2x TS2694 + TS2709 + TS2749 + TS2713 | all five mirrored |
| alias-chain-interface.ts | 1x TS2322 | 1x PITH2322 at the wrong member (two-link chain checks with the UNDERLYING display) |

Differential: 9/9 match on (code-family, message) multisets; declined
fixtures recorded as UNSUPPORTED with reasons, never silent, never forced.

Probed tsc rules pinned here: numeric literals check by VALUE (`1.0`
matches `1`; `0x2` spells `Type '2'`); string literals never match, even
member values (`Type '"a"'`); booleans spell literally (`Type 'true'`);
member accesses are clean; `const enum` is identical; ambient enums accept
everything; computed members fold; qualified annotations spell the
namespace-stripped name (`Dir`, `Dir.Up`, `Color.Red`); missing and
non-exported members both diagnose `TS2694` (qualifier names the resolved
prefix: `NS.Dir`, `Color`); single-name namespaces-as-types diagnose
`TS2709` while trailing qualified namespaces diagnose `TS2749` (the rule
is positional); qualifying past an interface diagnoses `TS2713`.

Pinned divergences (probe-recorded, fixtures or e2e-pinned): computed and
ambient enums decline; member-access and qualified-value initializers
decline (no expression facts); exported non-type members as types decline
(tsc `TS2749` — kind is unknowable without value facts, so never a wrong
`TS2694`); unresolved qualification heads skip silently (tsc `TS2503`,
the call-site precedent — covered by a dedicated e2e skip test, since a
baseline would mismatch by design).
