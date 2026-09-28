# check-multifile corpus (PITH-P019)

Multi-file programs: relative import specifiers resolve to `FileId`s, named
re-export chains and `export *` barrels resolve transitively, and each file
checks with cross-file name resolution (imported consts/functions/interfaces
usable at use sites with correct types). Oracle baselines are tsc 7.0.2 via
`.agent/scripts/pith-oracle/run.mjs` (normalized `file:TSNNNN: message`).
Fixtures share one directory with per-case filename prefixes
(`clean-main.ts` imports `./clean-shared`); the harness runs tsc per file
and tsc follows the relative imports, so `*-main` baselines cover the whole
case while `*-shared`/`*-mid` baselines pin the supporting files clean.

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| clean-main.ts (+ clean-shared.ts) | clean | silent (imported const, call, and interface annotation check) |
| error-main.ts (+ error-shared.ts) | 1x TS2322 (`Type 'string' …`) + 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2322 at the declarator + 1x PITH2345 at the argument |
| missing-main.ts (+ missing-shared.ts) | 1x TS2305 (at `NOPE`) + 1x TS2307 (at the specifier) | 1x PITH2305 at the imported-name span + 1x PITH2307 at the specifier span |
| chain-main.ts (+ chain-mid.ts, chain-shared.ts) | clean | silent (named re-exports resolve transitively) |
| barrel-main.ts (+ barrel-index.ts, barrel-shared.ts) | clean | silent (`export *` barrels resolve transitively) |

Differential: 5/5 match on the checkable subset (3 silent/clean +
2 diagnostic pairs). Probe rules (tsc 7.0.2, recorded in `pith-solver`
docs): `TS2305` anchors at the imported name (one per binding, nothing at
uses), `TS2307` fires once per statement at the specifier, re-export chains
and barrels are transparent, and interface annotations keep their
name-spelled elaborations across files.

Out of scope (declined with reasons, unit-pinned in
`e2e_check_multifile.rs`; no corpus fixture): default/namespace imports,
namespace re-exports, ambiguous star exports, re-export cycles, non-relative
specifiers (node_modules, tsconfig-paths), value uses of imported types
(oracle `TS2693`), function-typed value uses, and non-literal cross-file
initializers.
