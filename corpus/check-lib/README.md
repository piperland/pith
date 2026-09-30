# check-lib corpus (PITH-P034)

Lib type space, first cut: `Array<T>`/`T[]` and `Promise<T>` admit with
single primitive type arguments; every other lib shape declines with a
distinct reason. Oracle baselines are tsc 7.0.2 via
`.agent/scripts/pith-oracle/run.mjs` (normalized `file:TSNNNN: message`).

| Fixture | tsc 7.0.2 baseline | Solver verdict |
|---|---|---|
| array-correct.ts | clean | silent (all element kinds match, incl. empty and `any`) |
| array-wrong-member.ts | 4x TS2322 | 4x PITH2322 (literal order, one per wrong member) |
| array-suffix.ts | 2x TS2322 | 2x PITH2322 (`T[]` spelling + array-vs-primitive cross-shape) |
| promise-correct.ts | clean | silent (unwrapped payloads, incl. `Promise<Array<...>>` and `await`) |
| promise-wrong.ts | 4x TS2322 | 4x PITH2322 (incl. member-wise through `Promise<Array<...>>` and `await`) |
| tuple-declined.ts | clean | 1x UNSUPPORTED (tuples are not arrays) |
| record-declined.ts | clean | 1x UNSUPPORTED (utility types need lib modeling) |
| iterable-map-declined.ts | clean | 2x UNSUPPORTED (iterables, collections) |

Differential: 8/8 match on (code-family, message) multisets; declines are
recorded with reasons, never silent, never forced.

Probed tsc rules pinned here (`.agent/scratch/p034-probes/`): member-wise
`TS2322`s in literal order, one per wrong member; expected types always
spell the suffix form (`number[]`, even for `Array<number>`); empty arrays
spell `never[]`; mixed-kind arrays spell unions (`(string | number)[]` —
declined, never mis-spelled); non-literal members are silent (skipped);
`await` is transparent; non-async `Promise` returns spell `TS2322`/`TS2739`
the subset cannot spell (declined); `Promise<never>` spells literal types
(declined — no value facts); bare/multi-arg `Array`/`Promise` spell
`TS2314` (declined); array inits against object/interface annotations spell
the `TS2741`/`TS2739` missing family with the array spelling as actual.
