# check-generics corpus (PITH-P016)

Generic identity-style functions `function id<T>(x: T): T` with explicit
type arguments AND single-candidate inference from argument literals.
Oracle baselines are tsc 7.0.2 via `.agent/scripts/pith-oracle/run.mjs`
(normalized `file:TSNNNN: message`; `T`-elaboration continuation lines are
kept in the baselines and folded by the differential, like check-narrowing).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| explicit-correct.ts | clean | silent calls + 1 UNSUPPORTED (pass-through body declines) |
| explicit-wrong.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 at the argument + 1 UNSUPPORTED |
| inferred-correct.ts | clean | silent calls (T binds per literal) + 1 UNSUPPORTED |
| inferred-wrong.ts | 1x TS2322 (`Type 'string' … 'T'`) | 1x PITH2322 on the body (first line) + inference recorded |
| inference-failure.ts | clean | 2 UNSUPPORTED (body + no candidate for `u`) |
| multi-param-declined.ts | clean | 1 UNSUPPORTED (call skips; note covers it) |
| constrained-declined.ts | clean | 1 UNSUPPORTED |
| defaulted-declined.ts | clean | 1 UNSUPPORTED |
| union-member-declined.ts | 1x TS2322 (`Type 'string | T' …`) | 1 UNSUPPORTED |
| object-member-declined.ts | 1x TS2322 (`Type 'T' … '{ v: T; }'`) | 1 UNSUPPORTED |
| constrained-correct.ts | clean | silent calls (constraint satisfied) + 1 UNSUPPORTED (body) |
| constrained-wrong.ts | 1x TS2345 (inferred `number` vs constraint) + 1x TS2344 (explicit `number` violates) | 1x PITH2345 + 1x PITH2344 + 1 UNSUPPORTED (body) |
| defaulted-correct.ts | clean | silent calls (inferred `number`; explicit `string` overrides) + 1 UNSUPPORTED (body) |
| defaulted-inference-override.ts | 1x TS2345 (explicit `string` vs defaulted `number`) | 1x PITH2345 + 1 UNSUPPORTED (body) |
| conditional-return-declined.ts | 1x TS2322 on the body | 1 UNSUPPORTED (conditional return) |
| keyof-param-declined.ts | 1x TS2322 on the body (+ elaboration) | 1 UNSUPPORTED (keyof parameter) |
| mapped-return-declined.ts | 1x TS2353 on the body | 1 UNSUPPORTED (mapped return) |

Differential: 5 diagnostic pairs match (explicit-wrong TS2345,
inferred-wrong TS2322-first-line, constrained-wrong TS2345 + TS2344,
defaulted-override TS2345); 4 clean admission matches
(explicit/inferred/constrained/defaulted-correct); 9 declined fixtures
pin their divergence explicitly (inference-failure, multi-param,
constrained/defaulted-declined, union, object, keyof, conditional,
mapped). No generic declaration is ever decl-silent, by tsc's own
rule: literal bodies always fail against bare `T`, and pass-through
(`return x`) bodies need expression facts the adapter does not emit — so
every oracle-clean fixture pins a decline, never a false match.

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): inferred call
sites never error (T always binds; uses error instead, which needs
expression facts); bodies check against `T` directly and call-independently;
explicit count mismatches spell `TS2558` (`Expected 1 type arguments, but
got 2.`); multi-parameter/constraint/default shapes are oracle-clean while
union/object `T` positions error in tsc itself.

Out of scope (declined with reasons, unit-pinned where no corpus fixture
exists): nested `T` positions beyond union/object members (`T[]`, shaped
type arguments), `in`/`out`/`const` modifiers, multi-argument arity,
non-literal inference candidates.
