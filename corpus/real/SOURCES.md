# PITH-P021 real-project corpus — provenance (pinned, permissive licenses only)

All fixture files under `corpus/real/` are byte-verbatim copies of the
upstream sources below (no adaptation; license headers kept where present).
Verified 2026-09-29 by downloading each raw URL and comparing SHA-256
(`Invoke-WebRequest` + `Get-FileHash`; 5/5 IDENTICAL after one doc-comment
transcription slip in `plimit-stress/index.d.ts` was overwritten with the
upstream bytes — see task notes).

Reproduce: `curl -sL <raw URL> | sha256sum` and compare with `pinned sha256`.

| Case file(s) | Upstream project | Raw URL (pinned tag) | Tag | Commit (revision) | License | Pinned sha256 |
|---|---|---|---|---|---|---|
| `defu/src/defu.ts` (71 lines) | [unjs/defu](https://github.com/unjs/defu) (recursive defaults-merging utility) | https://raw.githubusercontent.com/unjs/defu/v6.1.7/src/defu.ts | v6.1.7 | `80c0146afb11ebd86183a579ec469f3abd976695` | MIT (© Pooya Parsa; `LICENSE` blob `e739abce…`) | `3AC1D2AD…4805D84DD` |
| `defu/src/_utils.ts` (26 lines) | unjs/defu (see above; fork note for sindresorhus/is-plain-obj retained in-file) | https://raw.githubusercontent.com/unjs/defu/v6.1.7/src/_utils.ts | v6.1.7 | `80c0146afb11ebd86183a579ec469f3abd976695` | MIT (same `LICENSE`; in-file fork credit kept) | `8B52FA19…85915C4` |
| `defu/src/types.ts` (100 lines) | unjs/defu (see above) | https://raw.githubusercontent.com/unjs/defu/v6.1.7/src/types.ts | v6.1.7 | `80c0146afb11ebd86183a579ec469f3abd976695` | MIT (same `LICENSE`) | `4DC8C0F4…13FE89A6EF4` |
| `destr/src/index.ts` (99 lines) | [unjs/destr](https://github.com/unjs/destr) (safe JSON parsing utility) | https://raw.githubusercontent.com/unjs/destr/v2.0.5/src/index.ts | v2.0.5 | `7bb3c39ef5f8c84219be08ebc11b3c4f4a4c828f` | MIT (© Pooya Parsa/unjs; `LICENSE` blob identical to defu's `e739abce…`, verified via git blob sha) | `CA1D205D…D69EC02E9A1` |
| `plimit-stress/index.d.ts` (138 lines) | [sindresorhus/p-limit](https://github.com/sindresorhus/p-limit) (concurrency limiter; **shipped declaration file = honest stress**) | https://raw.githubusercontent.com/sindresorhus/p-limit/v7.3.3/index.d.ts | v7.3.3 | `4d4ec71803d8736567249c3dde06ea82795ae7c7` | MIT (© Sindre Sorhus; `license` file fetched and checked) | `D367543C…7162514EE` |

Full sha256 values are in the runner evidence (`Get-FileHash` output in the
PITH-P021 report); prefixes above disambiguate. Tag→commit resolution via
`api.github.com/repos/<owner>/<repo>/tags` on 2026-09-29.

Selection rationale: `defu` (functions + recursive calls + objects +
`typeof`/structural narrowing fragments) and `destr` (unions, narrowing,
calls, regex/consts) exercise the M2 subset's neighborhood; `plimit-stress`
is the designated blow-up (ambient declarations, generic call signatures,
`Promise`/`Iterable` lib types — all established out-of-subset). `_utils.ts`
is 26 lines (just under the 30-line preference) and is included only to
close `defu.ts`'s relative-import set, per the allowed "relative imports
within the set" rule.
