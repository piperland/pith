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
| overloads-declined.ts | 1x TS2554 | 1x PITH2554 at the excess arg (P044 union arity) |
| overload-clean.ts | clean | silent (each call matches a different signature) |
| overload-first-match.ts | clean | silent (first match + later-only match) |
| overload-wrong-all.ts | 1x TS2769 + continuations | 1x PITH2769, message carries both continuations |
| overload-arity.ts | 2x TS2554 + 1x TS2575 | same (union `1-3`; gap names `1` and `3`) |
| overload-generic-declined.ts | 1x TS2769 + continuations | UNSUPPORTED (generic excluded distinctly) |
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
| named-param-call-declined.ts | 1x TS2345 (primitive control) | 1x PITH2345 + 1 UNSUPPORTED (opaque named param declines distinctly; oracle clean there — pinned divergence) |
| generic-param-declined.ts | clean | silent + 1 UNSUPPORTED (generic `T` declines exactly as before — pinned divergence) |
| named-structural-clean.ts | clean | silent (object arg checks member-wise against the local shape) |
| named-structural-wrong.ts | 3x TS2322 (1 + 2, one per wrong member) | 3x PITH2322 at the argument spans |
| named-structural-excess.ts | 1x TS2353 (interface-name spelling) | 1x PITH2353 at the argument span |
| named-structural-missing.ts | 1x TS2741 + 1x TS2739 | same, both spelling the interface name |
| named-structural-imported-declined.ts (+ `-dep.ts` support file, oracle-clean) | 1x TS2322 | 1 UNSUPPORTED (imported name claims no local shape — legacy decline; pinned divergence) |
| named-structural-methoded-declined.ts | clean | 1 UNSUPPORTED (methoded shape declines in the shared comparison; pinned divergence) |
| named-structural-nonliteral.ts | clean | 2 UNSUPPORTED (identifier arg declines distinctly, call result keeps the opaque decline; pinned divergences) |
| named-alias-call-declined.ts | 1x TS2322 | 1 UNSUPPORTED (no alias tables at call sites — opaque decline; pinned divergence) |
| ambient-clean.ts | clean | silent (2 ambient calls: arity + arg types match) |
| ambient-wrong-type.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 at the mismatched arg |
| ambient-too-few.ts | 1x TS2554 (`Expected 2 arguments, but got 1.`) | 1x PITH2554 at the callee |
| ambient-too-many.ts | 1x TS2554 (`Expected 1 arguments, but got 2.`) | 1x PITH2554 at the first excess arg |
| ambient-overload-clean.ts | clean | silent (each call matches a different ambient signature) |
| ambient-overload-wrong.ts | 1x TS2769 + continuations | 1x PITH2769, message carries both continuations |
| ambient-overload-generic-declined.ts | clean | silent + 1 UNSUPPORTED (generic ambient signature excluded distinctly; oracle instantiates `T` — pinned divergence) |
| overload-impl-excluded.ts | 1x TS2345 (`Argument of type 'boolean' …`) | 1x PITH2345 (implementation signature never participates) |
| ts2391-impl-less-group.ts | 1x TS2391 (on the declaration) + 1x TS2769 + continuations | 1x PITH2769 (calls still resolve; the declaration diagnostic stays declined) |
| non-callable-ambient-declined.ts | 1x TS2349 + continuation | UNSUPPORTED (bound name declares no function signature; the subset never spells `TS2349`) |

Differential: 27/27 match on the checkable direct-call subset (9
silent/clean + 18 diagnostic groups); 12/12 divergences pinned explicitly
(oracle errors while the solver declines or skips, or oracle clean while
the solver declines) — unresolved-callee silence (tracked once, never
double-diagnosed), required-after-optional shapes, generic overload
signatures, opaque named-param calls, generic `T` calls, imported-shape
calls, methoded-shape calls, non-literal shape args, alias-named
calls, generic ambient signatures, non-callable ambient shapes, and the
TS2391 declaration diagnostic are acknowledged non-goals, never silent
gaps. PITH-P044 converted
the old overload decline into matches (any-match resolution, union
arities, and the gap spelling). PITH-P037 converted the old
range/variadic declines into matches. PITH-P062 converted the local-shape
object-arg decline into matches (shared P017 comparison). PITH-P063
admitted ambient declarations into call resolution (single declarations
check like lone declarations; ambient groups resolve by any-match; the
implementation signature never participates) while keeping declaration
diagnostics (`TS2391`), generic/union ambient params, and non-callable
ambient shapes declined distinctly.

Member differential: 3/3 match on the checkable opaque subset (1 silent +
2 diagnostic groups); 3/3 divergences pinned explicitly —
`member-unknown-member` (oracle `TS2339`, solver one unsupported),
`member-unknown-receiver` (oracle `TS2304`, solver silent — tracked
unresolved), `member-lib-declined` (oracle clean, solver four
unsupported — range/overload/variadic lib shapes are acknowledged
non-goals, never silent gaps).

## P046 named (interface/alias) params

Call-site args against opaque (known interface/alias) params decline
distinctly per site — even a matching object arg cannot verify without
value facts, so arity never runs (the uncheckable-shape precedent).
Generic `T`, union, and complex param annotations decline exactly as
before (never the opaque reason). The call driver collects the scope
from the adapter's interface/alias facts; class constructors and
multifile calls thread an empty scope (pinned gaps — those paths keep
today's verdicts). Probes in `.agent/scratch/p046-probes/`.

## P062 structural admission for locally-shaped named params

Object-literal args against params naming a LOCAL interface shape check
member-wise through the shared P017 comparison (interface-name spelling,
wrong > excess > missing priority intact): `named-structural-clean`,
`named-structural-wrong`, `named-structural-excess`, and
`named-structural-missing` match their oracle families with zero
unsupported. The never-runs rule is gone for admitted shapes (arity runs
first, diagnostics stop at the first mismatch in argument order), while
everything else keeps declining distinctly: imported names
(`named-structural-imported-declined`, legacy decline — the
`-dep.ts` support file is oracle-clean), methoded shapes
(`named-structural-methoded-declined`, complex-member decline),
non-literal args (`named-structural-nonliteral`: identifiers
decline distinctly, call results keep the opaque decline), and
alias-named params (`named-alias-call-declined`, opaque decline — call
sites thread no alias tables). Object-literal members ride per-fixture
hand-fed driver tables (the adapter emits no call-argument member facts).
Probes in `.agent/scratch/p062-probes/`.

Structural differential: 4/4 match on the admitted subset (1 silent +
3 diagnostic groups); 4/4 divergences pinned explicitly —
`named-structural-imported-declined` (oracle `TS2322`, solver one
unsupported), `named-structural-methoded-declined` (oracle clean, solver
one unsupported), `named-structural-nonliteral` (oracle clean,
solver two unsupported), `named-alias-call-declined` (oracle `TS2322`,
solver one unsupported).

## P063 ambient overload declaration admission

Single `declare function` declarations check exactly like lone bodied
declarations (`ambient-clean` silent; `ambient-wrong-type` one `TS2345`;
`ambient-too-few`/`too-many` one `TS2554` each — no declaration
diagnostic for the missing body), and ambient overload groups resolve by
the P044 any-match (`ambient-overload-clean` silent;
`ambient-overload-wrong` one `TS2769` with continuations). The
implementation signature never participates (`overload-impl-excluded`:
one `TS2345` from the compatible signature, never an impl-shaped
verdict). Declined distinctly, never partial verdicts: generic ambient
signatures ride the existing exclusion (`ambient-overload-generic-declined`,
oracle clean — pinned divergence), union ambient params the existing
union decline (probed — generic/union instantiation stays out of scope),
missing
implementations keep the `TS2391` declaration diagnostic declined while
calls still resolve (`ts2391-impl-less-group`, oracle `TS2391` +
`TS2769` — pinned divergence), and calls to bound non-functions
(`declare const`, `non-callable-ambient-declined`) decline with the
no-signature reason (oracle `TS2349` plus a lib-spelled continuation —
pinned divergence). Probes in `.agent/scratch/p063-probes/`.

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): one family per
call site, arity beats arg types, only the first mismatched argument
reports; too-few anchors at the callee, too-many at the first excess
argument, arg-type at the mismatched argument. Overload rules (P044):
any-match across signatures (the implementation never participates);
all-fail spells `TS2769` with two continuation lines at the last
signature's first mismatch; admitted-by-none counts union to `TS2554` /
`TS2555`, or to the gap spelling `TS2575` strictly between ranges.

Out of scope (no facts, solver never sees them): method/member calls on
non-allowlisted receivers, computed members (`JSON["parse"]()`), optional
chains (`f?.()`, `JSON?.parse()`, `JSON.parse?.()`), chained receivers
(`a.b.c()`), spreads (`f(...xs)`), `super(...)`, `import(...)`, `new f()`,
tagged templates. Non-primitive parameter types decline per call with
reasons (unit-pinned; no corpus fixture).
Known-but-uncheckable lib members (`JSON.parse`, `JSON.stringify`,
`console.warn/log/error`, `Math.max/min`) and unknown members on known
receivers decline per site with lib reasons (corpus-pinned above).
