# check-classes corpus (PITH-P020)

Class declarations with annotated property initializers and constructor
parameter lists: property initializers against their annotations
(`PITH2322` <-> `TS2322`, reusing the const path) and `new C(...)` sites
against constructor parameters (`PITH2554` <-> `TS2554` arity,
`PITH2345` <-> `TS2345` arg types, reusing the call path). Oracle baselines
are tsc 7.0.2 via `.agent/scripts/pith-oracle/run.mjs` (normalized
`file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| correct.ts | clean | silent (inits match; ctor arity + arg types match) |
| prop-mismatch.ts | 1x TS2322 (`Type 'string' …`) | 1x PITH2322 at the property |
| ctor-arity.ts | 1x TS2554 (`Expected 2 arguments, but got 1.`) | 1x PITH2554 at the callee |
| new-argtype.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 at the mismatched arg |
| methods-declined.ts | 1x TS2322 (bad method return) | UNSUPPORTED (method bodies unchecked) |
| heritage-declined.ts | clean | UNSUPPORTED (heritage outside the subset) |
| accessors-declined.ts | 1x TS2322 (bad getter return) | UNSUPPORTED (accessors outside the subset) |
| abstract-declined.ts | clean | UNSUPPORTED (abstract semantics outside the subset) |

Differential: 4/4 match on the checkable subset (1 silent/clean +
3 diagnostic pairs); 4/4 divergences pinned explicitly (oracle errors or
stays clean while the solver declines) — method bodies, heritage,
accessors, and abstract forms are acknowledged non-goals, never silent gaps.

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): property
mismatches anchor at the property with const-shaped `TS2322`; `new`
too-few anchors at the callee, too-many at the first excess argument,
arg-type at the mismatched argument; implicit constructors take 0
arguments; `this`-assignments and missing initializers (`TS2564`) need flow
facts and decline.

Out of scope (facts record flags, solver declines with reasons): static
members, computed/non-identifier keys, decorators, index signatures,
generic classes, class expressions, `declare` classes, constructor
overloads, and `this`-assignments. `new` on non-identifier callees and
spreads emit no facts (mirroring call exclusions).
