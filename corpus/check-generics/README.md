# check-generics corpus (PITH-P016, multi-parameter PITH-P036, identifier-argument PITH-P061)

Generic identity-style functions `function id<T>(x: T): T` with explicit
type arguments AND single-candidate inference from argument literals,
extended to two or three independent type parameters (`function pair<T,
U>(x: T, y: U): T`) with per-parameter inference, explicit lists, and
per-position mismatch diagnostics — plus identifier-argument instantiation
(one level through the P048 table: literal or P060-inferred const kinds and
enclosing-function parameters bind per position; anything else declines).

Generic identity-style functions `function id<T>(x: T): T` with explicit
type arguments AND single-candidate inference from argument literals,
extended to two or three independent type parameters (`function pair<T,
U>(x: T, y: U): T`) with per-parameter inference, explicit lists, and
per-position mismatch diagnostics.
Oracle baselines are tsc 7.0.2 via `.agent/scripts/pith-oracle/run.mjs`
(normalized `file:TSNNNN: message`; `T`-elaboration continuation lines are
kept in the baselines and folded by the differential, like check-narrowing).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| explicit-correct.ts | clean | silent calls + 1 UNSUPPORTED (pass-through body declines) |
| explicit-wrong.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 at the argument + 1 UNSUPPORTED |
| inferred-correct.ts | clean | silent calls (T binds per literal) + 1 UNSUPPORTED |
| inferred-wrong.ts | 1x TS2322 (`Type 'string' … 'T'`) | 1x PITH2322 on the body (first line) + inference recorded |
| inference-failure.ts | clean | 2 UNSUPPORTED (body + non-literal-source decline for `u`) |
| multi-param-declined.ts | clean | silent calls (T, U bind per literal) + 1 UNSUPPORTED (body) |
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
| pair-correct.ts | clean | silent calls (T, U bind per literal) + 1 UNSUPPORTED (body) |
| pair-wrong-first.ts | 1x TS2345 (inferred `number` vs `string` constraint at the first argument) | 1x PITH2345 + 1 UNSUPPORTED (body) |
| pair-wrong-second.ts | 1x TS2345 (inferred `boolean` vs `number` constraint at the second argument) | 1x PITH2345 + 1 UNSUPPORTED (body) |
| pair-explicit-correct.ts | clean | silent calls (explicit `number, string` match) + 1 UNSUPPORTED (body) |
| pair-explicit-wrong.ts | 1x TS2345 (explicit second argument vs `string`) | 1x PITH2345 at the argument + 1 UNSUPPORTED |
| pair-explicit-count.ts | 2x TS2558 (`Expected 2 type arguments, but got 1/3.`) | 2x PITH2558 at each callee + 1 UNSUPPORTED |
| triple-correct.ts | clean | silent calls (A, B, C bind per literal) + 1 UNSUPPORTED (body) |
| pair-inference-failure.ts | clean | 2 UNSUPPORTED (body + non-literal-source decline for `T`) |
| ident-arg-clean.ts | clean | silent calls (T binds per identifier: inferred and annotated kinds) + 1 UNSUPPORTED (body) |
| ident-arg-wrong.ts | 1x TS2345 (inferred `number` from the annotated source vs constraint) | 1x PITH2345 at the argument + 1 UNSUPPORTED (body) |
| inferred-kind-arg.ts | 1x TS2345 (inferred `number` from the unannotated source vs constraint) | 1x PITH2345 at the argument + 1 UNSUPPORTED (body) |
| param-sourced-arg.ts | clean | silent call (T binds from the enclosing parameter) + 1 UNSUPPORTED (body) |
| cross-ident-pair.ts | clean | silent call (T, U bind per identifier position) + 1 UNSUPPORTED (body) |
| unresolvable-declined.ts | 1x TS2304 (`Cannot find name 'nope'.`) | 2 UNSUPPORTED (distinct identifier decline + body) |
| explicit-ident-clean.ts | clean | silent call (explicit `number` matches the resolved identifier kind) + 1 UNSUPPORTED (body) |
| explicit-ident-wrong.ts | 1x TS2345 (explicit `string` vs the resolved `number` identifier kind) | 1x PITH2345 at the argument + 1 UNSUPPORTED (body) |
| explicit-ident-unresolvable.ts | 1x TS2304 (`Cannot find name 'nope'.`) | silent call (explicit-path skip) + 1 UNSUPPORTED (body) |

Differential: 12 diagnostic pairs match (explicit-wrong TS2345,
inferred-wrong TS2322-first-line, constrained-wrong TS2345 + TS2344,
defaulted-override TS2345, pair-wrong-first/second TS2345,
pair-explicit-wrong TS2345, pair-explicit-count 2x TS2558,
ident-arg-wrong TS2345, inferred-kind-arg TS2345,
explicit-ident-wrong TS2345); 12 clean
admission matches (explicit/inferred/constrained/defaulted-correct,
multi-param-declined, pair-correct, pair-explicit-correct,
triple-correct, ident-arg-clean, param-sourced-arg, cross-ident-pair,
explicit-ident-clean);
11 declined fixtures pin their divergence explicitly
(inference-failure, pair-inference-failure, unresolvable-declined,
explicit-ident-unresolvable,
constrained/defaulted-declined, union, object, keyof, conditional,
mapped). No generic declaration is ever decl-silent, by tsc's own

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): inferred call
sites never error (each parameter binds from its own argument; uses error
instead, which needs expression facts); bodies check against the return
name directly and call-independently; explicit count mismatches spell
`TS2558` (`Expected 1 type arguments, but got 2.`, or the `1-2` range
with trailing defaults); explicit type-argument arity beats value arity,
which beats name resolution (every unknown name reports), which beats
satisfaction (first `TS2344` only), which beats argument checks (first
`TS2345` only); partial explicit lists fill trailing positions from
their defaults; union/object `T` positions error in tsc itself.

Out of scope (declined with reasons, unit-pinned where no corpus fixture
exists): more than three type parameters, required parameters after
optional ones (tsc `TS2706`), nested `T` positions beyond union/object
members (`T[]`, shaped type arguments), `in`/`out`/`const` modifiers,
non-identifier non-literal inference candidates, identifier sources beyond
single-level literal/parameter propagation (`let` bindings, depth-2+
chains, use-before-declaration, cross-file meanings — the P048 gates ride
through), duplicate bare names sharing one slot (tsc binds the literal
type — the P036 divergence), unresolvable explicit-path identifier
arguments (the explicit path skips per-argument as before — the P069
pinned divergence), empty
angle-bracket lists (tsc `TS1099`).
