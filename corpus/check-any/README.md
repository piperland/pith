# check-any corpus (PITH-P025)

`any`/`unknown` boundary plus `as`/`satisfies`/angle assertions. Oracle
baselines are tsc 7.0.2 via `.agent/scripts/pith-oracle/run.mjs`
(normalized `file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| any-const-correct.ts | clean | silent (`any` admits every literal) |
| any-param-correct.ts | clean | silent (`any` params accept every literal) |
| any-param-wrong.ts | 1x TS2345 (`Argument of type 'string' …`) | 1x PITH2345 (same) |
| any-return.ts | clean | silent (`any` returns admit every literal) |
| as-cast-admit.ts | 2x TS2322 | 2x PITH2322 (admitted results check on) |
| as-cast-decline.ts | 2x TS2322 + 2x TS2352 + 1x TS2345 + 1x TS2352 | 6x PITH (same multiset) |
| unknown-unguarded.ts | 1x TS2322 | UNSUPPORTED (pinned divergence, see below) |
| destr-transform.ts | clean | 2x UNSUPPORTED (pinned divergence, see below) |

Differential: 6/6 match on the checkable subset (3 silent/clean +
3 diagnostic multisets); 2/2 divergences pinned explicitly (oracle errors
or stays clean where the subset declines) — identifier-held `unknown`
flows and non-literal destr-shaped returns are acknowledged non-goals
with recorded reasons, never silent gaps.

Probe rules (tsc 7.0.2, recorded in `pith-solver` docs): `any` is silent
both directions; `unknown` annotations admit while `unknown` values
diagnose `TS2322`; `as`/angle admit on overlap (`TS2352` otherwise) with
the target flowing downstream; `satisfies` admits on the same overlap but
stays transparent to the operand (`TS1360` otherwise); declined casts
never suppress the downstream check (both families fire).

Pinned divergences:

- `unknown-unguarded`: `const a: string = uv` (identifier-held `unknown`)
  diagnoses `TS2322` in tsc; the solver records one unsupported
  (non-literal initializer — no value-type facts) plus one for the
  `declare const` itself (missing initializer — the pre-existing
  ambient-declaration pin).
- `destr-transform`: `jsonParseTransform` plus the `destr` return shape
  (`any` params, `unknown` return, `value as unknown`) are clean in tsc;
  the solver records two unsupported (one non-literal return plus one
  complex cast operand — identifier operands never classify).

Out of scope (declined with reasons, never mis-verdicted): object/union/
literal targets (`"x" as { a: number }` spells oracle `TS2352` — the
subset cannot spell canonical targets from sliced text), casts under
named-interface/enum annotations (solver declines as non-literal inits),
`never` annotations/parameters beyond the unit pins (no corpus fixture),
assertion arguments at `new`-expression, class-property, and
returned-object-member positions (no cast channel there — they degrade to
`NonLiteral` like any other unmodeled expression).
