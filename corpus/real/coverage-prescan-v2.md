# PITH-P026 coverage pre-scan v2 (STRICT, hand-authored 2026-09-29)

Re-scores every P021 top-level construct against the M3 subset. Rule is
unchanged and strict: IN-subset ONLY if the pipeline would VERDICT the
construct today (silent check or diagnostic) — not merely parse/bind it,
and not record it as unsupported/declined. When in doubt, out-of-subset.
M3 precedents cited per flip; everything else confirms its v1 decline.

M3 subset (differential-pinned, tsc 7.0.2 oracle):
- P022 value imports (P019 clean/checked + P022 mirrors): resolved VALUE
  imports check silent; failed value imports diagnose PITH2305/PITH2307.
  `import type` failures DECLINE with reasons (pinned divergence — aliases
  emit no facts, diagnosing risks false verdicts). Default/namespace
  imports, re-export cycles, non-relative specifiers: still out (P019).
- P023 join returns: SingleReturn + exactly three joins (SequenceReturns:
  `return;return`, GuardReturn: `if(c)<divergent return>` + tail return,
  BranchReturns: `if/else` one return each) check per-position. Bare
  returns, multi-statement branches, loops, switch, try, throw, continue,
  else-if chains, if/else+tail: still Complex.
- P024 member calls: opaque arity/arg-type verdicts ONLY on allowlisted
  receivers (`Math.floor/pow`, `Array.isArray`, `Object.keys`). Known lib
  shapes (`JSON.parse/stringify`, `console.*`, `Math.max/min`) DECLINE per
  site with lib reasons; non-allowlisted receivers emit no facts; chained
  receivers (`a.b.c()`), computed members, spreads: out of scope.
- P025 any/casts: `any` admits every literal both directions (silent);
  `unknown` ANNOTATIONS admit, `unknown` VALUES diagnose TS2322
  (identifier-held unknown flows: pinned unsupported); `as`/angle admit on
  overlap with target flowing downstream (TS2352 otherwise); casts under
  named-interface/enum or object/union targets DECLINE as non-literal.

Result up front: **1/33 top-level constructs in-subset (3%)**, 0 unknown.
Delta vs P021 (0/33): **+1 — defu.ts #1** (value import now resolves
silent through the P022 checked graph). All other 32 declines confirmed
below against the new subset; each still hits at least one established,
unit-pinned reason M3 did not touch.

## defu/src/_utils.ts — 0/1 (no change)

| # | Construct | Verdict | Reason (v2 confirm) |
|---|---|---|---|
| 1 | `export function isPlainObject(value: unknown): boolean` | OUT | 6-statement body (if/if/if/if/const/return) — P023 admits at most 2-statement joins, so still Complex; `unknown` param annotation admits (P025) but the body kills the decl. `in` operator (no facts, P015); `Object.getPrototypeOf` non-allowlisted receiver (no facts, P024); `Object.prototype.toString.call` chained receiver (out of scope, P024). Four independent blockers. |

## defu/src/defu.ts — 1/9 (+1)

| # | Construct | Verdict | Reason (v2 confirm) |
|---|---|---|---|
| 1 | `import { isPlainObject } from "./_utils"` | **IN** | **FLIP.** Value import of a facted export (`export function` in-set, relative specifier) resolves through the checked graph and checks silent — exactly the P022 `checked-utils.ts` `isEven` precedent (P019 clean-main silent + P022 value-import mirrors). |
| 2 | `import type {...} from "./types"` | OUT | Type-only import naming pure aliases (no value facts in target) fails resolution and DECLINES with reasons per the P022 import-type policy (pinned divergence) — decline is not a verdict. |
| 3 | `function _defu<T>(...)` | OUT | Generic decl (constrained-declined, P016 — M3 untouched); `for..of` + `continue` + 5 returns (P023: loops/continue still Complex); `as Record<string,any>` object-target casts decline (P025 out-of-scope). `any` params admit (P025) but cannot save the decl. |
| 4 | `export function createDefu(merger?: Merger)` | OUT | Optional param + rest param (P014 exclusions, M3 untouched); arrow-function return is non-literal; `arguments_.reduce` non-allowlisted receiver (no facts, P024). |
| 5 | `export const defu = createDefu() as DefuInstance` | OUT | `as` target is a named interface → solver declines as non-literal init (P025 out-of-scope); unannotated const with call init (P012). |
| 6 | `export default defu` | OUT | Default export — P019 out-of-scope (default/namespace imports unit-pinned; no M3 fixture). |
| 7 | `export const defuFn = createDefu((object, key, currentValue) => …)` | OUT | Arrow callback (P013); unannotated params = implicit-any decline (P025 covers `any` ANNOTATIONS, not missing ones); element assignment (no index facts). |
| 8 | `export const defuArrayFn = …` | OUT | Same as #7 (`Array.isArray` verdicts only as a checked call site on literals — P024 — it cannot admit an unannotated arrow decl). |
| 9 | `export type { … } from "./types"` | OUT | Type-only re-export of aliases with no facts — same family as #2 (nothing to resolve or check; P019 barrels/chains cover value re-exports only). |

## defu/src/types.ts — 0/10 (no change)

Aliases, conditional/mapped/`infer`/`keyof`/`Omit` types, and the
`DefuInstance` interface (generic call signatures + method members,
optional `merger?`): M3 added no alias/interface/generic/conditional
machinery (P022 explicitly: aliases emit no facts). All 10 OUT as in v1.

## destr/src/index.ts — 0/9 (no change)

| # | Construct | Verdict | Reason (v2 confirm) |
|---|---|---|---|
| 1–3 | 3× regex consts | OUT (×3) | Regex-literal inits, unannotated (P009; no M3 regex facts). |
| 4 | `function jsonParseTransform(key: string, value: any): any` | OUT | Params/return (`string`, `any`, `any`) all admit under P025 — but the body is `[if{call + BARE return}, return value]`: the if-branch is two statements ending in a bare return, not a divergent return, so not GuardReturn (P023: bare returns stay Complex). `in` operator (no facts). Closest call of the trial, still firmly out. |
| 5 | `function warnKeyDropped(key: string): void` | OUT | `void` return excluded (P013/P023 void gap, M3 untouched); `console.warn` is lib-declined per site (P024 — mirrors this exact site). |
| 6 | `export type Options = { strict?: boolean }` | OUT | Optional member (P017, M3 untouched). |
| 7 | `export function destr<T = unknown>(…)` | OUT | Defaulted type param (P016 defaulted-declined, M3 untouched); body has switch + try/catch + throw + ~10 `as T` casts onto a type param (P023/P025 untouched). |
| 8 | `export function safeDestr<T = unknown>(…)` | OUT | Generic-defaulted (P016); spread `{…options}` (P014, no spread facts); explicit-args `destr<T>` call whose callee (#7) declines. |
| 9 | `export default destr` | OUT | Default export (same as defu #6). |

## plimit-stress/index.d.ts — 0/4 (no change, designated blow-up)

Method/generic signatures, ambient `declare`-shaped `pLimit` (NoBody
decline, P013), union param, optional member, `Pick<>`/`Promise`/
`Iterable` lib types: none touched by M3 (no generics/ambient/lib work).
All 4 OUT as in v1.

## Totals

33 top-level constructs: **1 in-subset, 32 out-of-subset, 0 unknown →
3% strict subset coverage** (P021: 0/33, 0%). The single flip is the
module-system gap closing for one shape; every other construct still hits
an established decline reason.

## Gap ranking v2 (top-level-construct hits; M3 planning signal, no fix promised)

1. Module system: 25 statements still carry declining module shapes
   (type-only imports/re-exports of aliases, default exports) — was 26/33,
   now 25/33 with one value import resolved.
2. Generics (params, constraints, defaults, `infer`, generic sigs, type
   args): ~17/33 — untouched by M3.
3. Non-join bodies (multi-return beyond 2-position joins, loops, switch,
   try/catch, bare returns): 6 function bodies — P023 narrowed but none of
   these six fit the three admitted joins.
4. `any`/`unknown`/implicit-any + `as` casts: params/returns now admit
   (P025) but zero top-level decls are saved — bodies/generics decline
   first. `console.warn`/`JSON.parse` lib-decline reasons now mirror the
   destr sites exactly (P024).
5. Member calls on non-allowlisted receivers (`Object.getPrototypeOf`,
   `.reduce`, `.test/.slice/.trim/.toLowerCase/.indexOf`, `.toString`,
   chained `.call`): no facts — 8 bodies.
6. Advanced types, optional/default/rest, lib/ambient types, expr-level
   rest (`in`, indexing, spreads, regex, `void`, template literals,
   `throw`): unchanged.

Qualitative (NOT counted): `Array.isArray(value)` (defu line 27) and
`Object.keys(…)` (defu line 12) are now allowlisted member shapes (P024)
firing inside declined bodies; `isPlainObject`'s typeof-guard lines and
destr's `typeof value !== "string"` early-return remain exact P015/P023
fragments. The checker is adjacent to these bodies — one import shape
already crossed over.
