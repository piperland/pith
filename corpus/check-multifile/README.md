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
| checked-main.ts (+ checked-utils.ts, checked-types.ts) | 1x TS2322 (`Type 'string' …`) + 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2322 at the declarator + 1x PITH2345 at the argument; imported const/function/interface/enum values with correct types check clean |
| iface-main.ts (+ iface-mid.ts, iface-shared.ts) | 1x TS2322 (`Type 'string' …`) + 1x TS2741 (`Property 'y' is missing … 'Point'`) | 1x PITH2322 at the wrong member + 1x PITH2741 spelling the re-exported interface; the clean use is silent |
| alias-main.ts (+ alias-mid.ts, alias-shared.ts) | 2x TS2322 (`Type 'string' …`) | 2x PITH2322: the interface alias expands to the underlying shape (member anchor), the primitive alias behaves exactly like its target spelling |
| typestar-main.ts (+ typestar-index.ts, typestar-shared.ts) | 1x TS2322 (`Type 'string' …`) | 1x PITH2322 at the wrong member; the star-barrel alias checks clean through the same expansion |
| typecyc-main.ts (+ typecyc-a.ts, typecyc-b.ts) | 2x TS2303 (`Circular definition of import alias 'Cyc'`, on the re-export statements) | no diagnostics; declines with reasons (the cyclic import plus the uncheckable annotation) — pinned gap, asserted explicitly in `e2e_check_multifile.rs`, not differentially |

Differential: 9/9 match on the checkable subset (3 silent/clean +
6 diagnostic multisets). Probe rules (tsc 7.0.2, recorded in `pith-solver`
docs): `TS2305` anchors at the imported name (one per binding, nothing at
uses), `TS2307` fires once per statement at the specifier, re-export chains
and barrels are transparent, interface annotations keep their
name-spelled elaborations across files, and aliases expand transparently
(missing members spell the underlying interface).

Out of scope (declined with reasons, unit-pinned in
`e2e_check_multifile.rs`; no differential corpus fixture): default/namespace imports,
namespace re-exports, ambiguous star exports, non-relative
specifiers (node_modules, tsconfig-paths), value uses of imported types
(oracle `TS2693`), function-typed value uses, non-literal cross-file
initializers, over-deep/cyclic/generic/complex alias targets (chains resolve
transitively up to the shared depth bound — a pinned divergence where tsc,
which has no limit, keeps resolving), and failed
`import type` resolutions (diagnosing would risk false verdicts where tsc
stays clean — a pinned divergence; value imports keep the exact
`PITH2305`/`PITH2307` mirrors). Re-export cycles keep corpus fixtures
(`typecyc-*`) with recorded `TS2303` oracle baselines, asserted explicitly
(declines with reasons, never differentially).
