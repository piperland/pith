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
| rest-param-declined.ts | clean | UNSUPPORTED (variadic arity outside the exact-count subset) |

Differential: 5/5 match on the checkable subset (2 silent/clean +
3 diagnostic pairs); 3/3 divergences pinned explicitly (oracle errors or
stays clean while the solver declines or skips) — overload resolution,
range/variadic arities, and unresolved-callee silence are acknowledged
non-goals, never silent gaps.

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): one family per
call site, arity beats arg types, only the first mismatched argument
reports; too-few anchors at the callee, too-many at the first excess
argument, arg-type at the mismatched argument.

Out of scope (no facts, solver never sees them): method/member calls,
optional chains (`f?.()`), spreads (`f(...xs)`), `super(...)`,
`import(...)`, `new f()`, tagged templates. Optional/defaulted params and
non-primitive parameter types decline per call with reasons (unit-pinned;
no corpus fixture).
