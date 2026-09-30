# check-calls corpus (PITH-P014)

Direct `f(...)` call sites checked against resolved function declarations:
exact-arity (`PITH2554` <-> `TS2554`) and literal-argument types against
annotated parameter types (`PITH2345` <-> `TS2345`). Oracle baselines are
tsc 7.0.2 via `.agent/scripts/pith-oracle/run.mjs` (normalized
`file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| correct.ts | clean | silent (2 calls: arity + arg types match) |
| too-few.ts | 1x TS2554 (`Expected 2 arguments, but got 1.`) | 1x PITH2554 at the callee |
| too-many.ts | 1x TS2554 (`Expected 2 arguments, but got 3.`) | 1x PITH2554 at the first excess arg |
| wrong-arg-type.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 at the mismatched arg |
| unresolved-callee.ts | 1x TS2304 | silent (already tracked as unresolved; never double-diagnosed) |
| method-call-excluded.ts | clean | silent, zero call facts (methods out of scope) |
| overloads-declined.ts | 1x TS2554 | UNSUPPORTED (multiple declarations; resolution is future work) |
| rest-param-declined.ts | clean | silent (PITH-P037: rest admits 1-or-more; converts the old variadic decline) |
| range-correct.ts | clean | silent (optional + defaulted ranges admit every call, incl. explicit `undefined`) |
| range-too-few.ts | 1x TS2554 (`Expected 1-2 arguments, but got 0.`) | 1x PITH2554 at the callee |
| range-too-many.ts | 1x TS2554 (`Expected 1-2 arguments, but got 3.`) | 1x PITH2554 at the first excess arg |
| range-wrong-type.ts | 2x TS2345 (`Argument of type 'string' …`) | 2x PITH2345, one per site at the mismatched arg |
| rest-prefix.ts | 1x TS2345 + 1x TS2555 | same (rest extras check the element type; below-minimum spells `Expected at least 1 arguments …`) |
| required-after-optional-declined.ts | 1x TS1016 (on the declaration) | UNSUPPORTED (required-after-optional; the solver spells no declaration diagnostics) |
| member-correct.ts | clean | silent (4 member calls: opaque arity + arg types match) |
| member-wrong-type.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 at the mismatched arg |
| member-arity.ts | 2x TS2554 (too-few + too-many) | 2x PITH2554, one per site |
| member-unknown-member.ts | 1x TS2339 (`Property 'nope' …`) | UNSUPPORTED (unknown member; full lib types out of scope) |
| member-unknown-receiver.ts | 1x TS2304 | silent, zero member facts (tracked unresolved; never double-diagnosed) |
| member-lib-declined.ts | clean | 4x UNSUPPORTED (range/overload/variadic lib shapes) |

Differential: 11/11 match on the checkable direct-call subset (4
silent/clean + 7 diagnostic groups); 3/3 divergences pinned explicitly
(oracle errors while the solver declines or skips) — unresolved-callee
silence (tracked once, never double-diagnosed), overload resolution, and
required-after-optional shapes are acknowledged non-goals, never silent
gaps. PITH-P037 converted the old range/variadic declines into matches.

Member differential: 3/3 match on the checkable opaque subset (1 silent +
2 diagnostic groups); 3/3 divergences pinned explicitly —
`member-unknown-member` (oracle `TS2339`, solver one unsupported),
`member-unknown-receiver` (oracle `TS2304`, solver silent — tracked
unresolved), `member-lib-declined` (oracle clean, solver four
unsupported — range/overload/variadic lib shapes are acknowledged
non-goals, never silent gaps).

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): one family per
call site, arity beats arg types, only the first mismatched argument
reports; too-few anchors at the callee, too-many at the first excess
argument, arg-type at the mismatched argument.

Out of scope (no facts, solver never sees them): method/member calls on
non-allowlisted receivers, computed members (`JSON["parse"]()`), optional
chains (`f?.()`, `JSON?.parse()`, `JSON.parse?.()`), chained receivers
(`a.b.c()`), spreads (`f(...xs)`), `super(...)`, `import(...)`, `new f()`,
tagged templates. Non-primitive parameter types decline per call with
reasons (unit-pinned; no corpus fixture).
Known-but-uncheckable lib members (`JSON.parse`, `JSON.stringify`,
`console.warn/log/error`, `Math.max/min`) and unknown members on known
receivers decline per site with lib reasons (corpus-pinned above).
