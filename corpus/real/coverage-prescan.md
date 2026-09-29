# PITH-P021 coverage pre-scan (STRICT, hand-authored 2026-09-29)

Rule: every TOP-LEVEL statement gets exactly one of
in-subset / out-of-subset (with decline reason + subset precedent) /
unknown. Strict: when in doubt, out-of-subset. Precedents cite existing
`corpus/check-*` READMEs (P009–P020). verdicts describe the CURRENT subset;
nothing here changes checker code (PITH-P021 forbids `crates/*` edits).

Result up front: **0/33 top-level constructs in-subset (0%)**, 0 unknown.
Every decline below hits an already-established, unit-pinned reason — the
trial measures the gap, it does not move it. Partial-credit fragments
(typeof-guard lines, primitive-annotated params, direct calls *inside*
declined bodies) are noted qualitatively and NOT counted.

## defu/src/_utils.ts — 0/1

| # | Construct | Verdict | Reason (precedent) |
|---|---|---|---|
| 1 | `export function isPlainObject(value: unknown): boolean` | OUT | 4 returns + branching (multi-return UNSUPPORTED, P013; flow-phase gap, P013 `branching.ts`); `unknown` param (non-primitive params decline, P014); `Object.*`/`.call` member calls + `in` operator (no facts, P014 exclusions; non-typeof guard, P015) |

## defu/src/defu.ts — 0/9

| # | Construct | Verdict | Reason (precedent) |
|---|---|---|---|
| 1 | `import { isPlainObject } from "./_utils"` | OUT | module imports are future work (P010 multifile tracks facts, but real module resolution is not in the checking subset) |
| 2 | `import type {...} from "./types"` | OUT | type-only import, same as #1 |
| 3 | `function _defu<T>(baseObject: T, defaults: any, …)` | OUT | generic fn (constrained use counts as constrained-declined, P016); default param (P014 exclusions); `any` params; 5 returns + `for..of` + `continue` (P013); `as` casts; recursion is a direct call but callee is generic (P016: calls check, bodies decline — here the declaration itself declines) |
| 4 | `export function createDefu(merger?: Merger)` | OUT | optional param (P014 exclusions); rest param (rest-param-declined, P014); arrow-function body (no facts, P013); `.reduce` member call (P014 exclusions) |
| 5 | `export const defu = createDefu() as DefuInstance` | OUT | `as`-cast (no cast facts); unannotated const with call init (non-literal init UNSUPPORTED, P012 `object-out-of-subset.ts`) |
| 6 | `export default defu` | OUT | module boilerplate, same as #1 |
| 7 | `export const defuFn = createDefu((object, key, currentValue) => …)` | OUT | arrow callback (P013); unannotated params = implicit-any decline (P013 `unannotated-param.ts`); `typeof x === "function"` guard (non-primitive typeof, cf. P015 complex/nontypeof declines); element assignment `object[key] =` (no index facts) |
| 8 | `export const defuArrayFn = …` | OUT | same as #7 + `Array.isArray` guard (non-typeof guard, P015 `nontypeof-guard.ts`) |
| 9 | `export type { … } from "./types"` | OUT | re-export, same as #1 |

## defu/src/types.ts — 0/10

| # | Construct | Verdict | Reason (precedent) |
|---|---|---|---|
| 1 | `export type Input = Record<string \| number \| symbol, any>` | OUT | generic-utility instantiation + `any` (nested-`T`/shaped type-argument positions out, P016) |
| 2 | `export type IgnoredInput = boolean \| number \| null \| any[] \| …` | OUT | union with `any[]` + `Record<never, any>` (union-annotation UNSUPPORTED, P009; shaped args, P016) |
| 3 | `export type Merger = <T extends Input, K extends keyof T>(…) => any` | OUT | constrained generic signature + `keyof` (constrained-declined, P016) |
| 4 | `type nullish = null \| undefined \| void` | OUT | union alias (union-annotation UNSUPPORTED, P009); `void` constituent (void gap, P013) |
| 5 | `export type MergeObjects<…> = … conditional …` | OUT | conditional + mapped + `Omit`/`&` (no conditional/infer facts anywhere in subset) |
| 6 | `export type Defu<…> = … infer …` | OUT | `infer` + recursion over conditionals, same as #5 |
| 7 | `export type DefuFn = <Source…, Defaults…>(…) => Defu<…>` | OUT | generic call signature resolving to conditional (P016) |
| 8 | `export interface DefuInstance { … }` | OUT | generic call signatures + method-shaped members inside (iface-methods-declined, P017); `extend(merger?: …)` optional param |
| 9 | `export type MergeArrays<…> = … infer …` | OUT | same as #5/#6 |
| 10 | `export type Merge<…> = nested conditional …` | OUT | 6-deep conditional over `Function`/`RegExp`/`Promise` lib types, same as #5 |

## destr/src/index.ts — 0/9

| # | Construct | Verdict | Reason (precedent) |
|---|---|---|---|
| 1–3 | `const suspectProtoRx / suspectConstructorRx / JsonSigRx = /…/` | OUT (×3) | regex-literal inits need inference (no-annotation UNSUPPORTED, P009); no regex facts |
| 4 | `function jsonParseTransform(key: string, value: any): any` | OUT | `any` params/return (non-primitive decline, P014); 3 returns incl. bare `return;` (P013); `in` operator (P015 nontypeof family); direct call to `warnKeyDropped` is checkable-shaped but the declaration itself declines |
| 5 | `function warnKeyDropped(key: string): void` | OUT | `void` return excluded (P013); template literal + `console.warn` member call (P014 exclusions) |
| 6 | `export type Options = { strict?: boolean }` | OUT | optional member (iface-optional-declined, P017) |
| 7 | `export function destr<T = unknown>(value: any, options: Options = {}): T` | OUT | defaulted type param (defaulted-declined, P016); `any`; default value param; `switch` + `try/catch` + `throw` (no flow facts beyond typeof guards, P015); 10 `as T` casts; element indexing `value[0]` |
| 8 | `export function safeDestr<T = unknown>(…)` | OUT | generic-defaulted (P016); object spread `{…options}` (no spread facts, P014); `destr<T>` explicit-args call is subset-shaped but callee #7 declines |
| 9 | `export default destr` | OUT | module boilerplate (as defu #6) |

## plimit-stress/index.d.ts — 0/4 (designated blow-up)

| # | Construct | Verdict | Reason (precedent) |
|---|---|---|---|
| 1 | `export type LimitFunction = { … }` | OUT | method signatures + generic method `map<Input, ReturnType>` + generic call signature (P016/P017); `Promise`/`PromiseLike`/`Iterable` lib types (no lib facts); `readonly` is assignability-neutral (P017) but doesn't save the rest |
| 2 | `export default function pLimit(concurrency: number \| Options): LimitFunction` | OUT | ambient declaration without body in `.d.ts` (`declare function` declines, P013); union param (P009) |
| 3 | `export type Options = { readonly concurrency: number; readonly rejectOnClear?: boolean }` | OUT | optional member (P017), same as destr #6 |
| 4 | `export function limitFunction<Arguments…, ReturnType>(…): … & Pick<…>` | OUT | generic + `Pick<>` utility + `Promise` (P016 shaped-args/out-of-scope) |

## Totals

33 top-level constructs: **0 in-subset, 33 out-of-subset, 0 unknown → 0% strict subset coverage.** No genuine unknowns: every construct hits an established decline reason (module system, generics, flow, `any`/casts, member calls, advanced types, optional/default/rest, lib types).

## Gap ranking (by top-level-construct hits; drives M3 planning, no fix promised)

1. Module system (`import`/`export`/`default`/re-export/type-import): 26/33 statements carry it. Biggest single blocker to "check a real file end-to-end".
2. Generics (params, constraints, defaults, `infer`, generic sigs, type args): ~17/33.
3. Bodies beyond straight-line single-return (multi-return, loops, `switch`, `try/catch`, `continue`, bare `return`): 6 function bodies.
4. `any`/`unknown`/implicit-any + `as` casts: ~10 constructs.
5. Member/method calls + property access on values (`Object.*`, `.reduce`, `JSON.parse`, `console.*`, `.test`, `.call`): 8 bodies.
6. Advanced types (conditional/mapped/`keyof`/`Omit`/unions-with-`any`): 9 aliases.
7. Optional/default/rest params + optional members: 7 constructs.
8. Lib types (`Promise`, `Iterable`, `RegExp`, `Function`) + ambient `.d.ts` declarations: 4 constructs.
9. Regex literals, `void`, template literals, `throw`, `in`, indexing, spreads: 8 (expression-level, concentrated in destr).

Qualitative (NOT counted): `isPlainObject`'s `value === null` / `typeof value !== "object"` lines and destr's `typeof value !== "string"` early-return are exactly the P015 typeof-guard shape — the subset's narrowing machinery would fire on these fragments if the enclosing declarations were ever admitted. That is M3 scoping signal, not coverage.
