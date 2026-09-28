# check-interfaces corpus (PITH-P017)

Interface-typed consts checked against interface member facts, plus
declaration-merging depth (interface+value pairs). Oracle baselines are tsc
7.0.2 via `.agent/scripts/pith-oracle/run.mjs` (normalized
`file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| iface-correct.ts | clean | silent (const + `let`, all shapes match) |
| iface-wrong-member.ts | 2x TS2322 | 2x PITH2322 |
| iface-missing-member.ts | 1x TS2741 | 1x PITH2741 (expected spells `User`) |
| iface-excess-member.ts | 1x TS2353 | 1x PITH2353 (expected spells `Point`) |
| iface-merged-pair.ts | clean | 2x UNSUPPORTED (unannotated `Foo`, non-literal value use) + silent interface-annotated use |
| iface-heritage-declined.ts | clean | 1x UNSUPPORTED (heritage clause) |
| iface-methods-declined.ts | clean | 2x UNSUPPORTED (method member, index member) |
| iface-optional-declined.ts | clean | 2x UNSUPPORTED (optional member, one note per use) |

Differential: 8/8 match on (code-family, message) multisets; declined
fixtures recorded as UNSUPPORTED with reasons, never silent, never forced.

Probed tsc rules pinned here: interface elaborations spell the interface
NAME in expected position (`... required in type 'User'.`, `... does not
exist in type 'Point'.`, `Type 'number' is not assignable to type
'Point'.`); wrong members diagnose per-member `TS2322` with member type
names; priority wrong > excess > missing holds; `readonly` is ignored by
assignability; merged interface+value pairs share one symbol (no merge
error; each meaning checks under its own rules).
