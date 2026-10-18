# M8 verdict: PASS — the wall is measured, not asserted: 26→23 executed, every survivor classified, hard lines hold

Date: 2026-10-18. Oracle: tsc 7.0.2. Toolchain: rustc 1.98.1 (Linux E2B).
Trial engine: P081–P083 at `20477b9` (clean tree), box `ikuotezjjfqtefgxvq0v9`.

## Verdict logic

M7 closed by declaring the thesis wall — six blocker classes it said no
in-subset primitive could cross, with one falsifiable crack: three destr
notes were banked as "needs value facts the subset refuses to invent". M8
tested that claim by execution. It broke the crack: all three notes
converted through three law-compliant primitives (P081 enclosing-function
params, P082 same-file direct effect arm, P083 return-tail ident seam), and
the re-trial (P084) re-measured the wall at 23 executed notes, 3/3 runs
byte-identical, 5/5 corpus pins matched, 844-test suite green, coverage
holding 1/33 EXECUTED. Every remaining note now has an evidence-backed
blocker class; the declared hard lines (no type-operator evaluation, no
control flow, no interprocedural resolution, no invented structure per
H-002) each name exactly which surviving notes they fence.

M8 is PASS in the same sense M7 was: not because the wall fell — it did not
— but because the loop proved it is real where it says it is real, and
wrong where it was wrong, with the correction banked as three accepted
conversions and one honest falsification chain.

## Per-thread basis

- P081 enclosing-function params for multifile const uses (`4b3bd31` +
  `aaa64cf` + `1f62e7f`): body_scope→params index from P080 facts, innermost
  bounded walk, threaded per-declarator into the enum entry's IdentTable at
  BOTH check time and input-build time (the CTO repair that made bare-receiver
  call upgrades see params). lib 327→329. 838→ green. Independent verifier
  PASS including the disclosed plumbing scope deviation. Its first live
  capture recorded "_value still declines" from a stale pre-fix run — the
  same-session correction and the P084 trial settle `_value` EXECUTED silent
  on 3/3 fresh runs.
- P082 same-file direct effect calls (`bb45ed8` + `9971189`): guard-arm and
  lone-effect direct calls admit iff exactly one same-file void-annotated
  required-param callee at exact arity. 6 unit gates (admits + 5 byte-
  identical negatives); fixture-level conversion executed (nonallowlist →
  direct-admits flip). HEADLINE FALSIFIED HONESTLY: predicted destr 24→23;
  executed 24 with reason refinement (arm admits, the tail gate fires).
  Accepted under the P073/P078 precedent. lib 329→335, suite 844.
- P083 return-tail ident seam (`20477b9`): driver-only mirror of the
  check-functions P048 seam — guard-effect tails slice bare-identifier
  returns, `return value;` resolves against the `value: any` param through
  machinery that already existed. jsonParseTransform EXECUTED silent, destr
  4→3, total 24→23, first-pass green with zero repairs, verifier PASS.
- P084 M8 re-trial (this doc + `corpus/real/results-template.md` P084
  section): unchanged drivers ×3, EXIT=0, notes 23/23/23,
  IDENTICAL_3_OF_3 normalized verdict lines, 5/5 sha pins, walls defu 3/0
  destr 1/0 plimit 1/0 medians (no comparison claims).

## Real-corpus walk (executed, n=23)

1. Named/generic param types — 7 (`T` ×3, `Merger` ×3, `Options` ×1).
   Blockers: `T` instantiation from non-literal args; `Merger` needs
   generic-alias keyof/indexed/conditional evaluation — the declared
   type-operator hard line; `Options` needs alias-to-object param admission
   + argument-member facts + multifile named-type scope — probed
   (tsc 7.0.2 pins excess/misfit/missing families with spreads present),
   planned as the P085→P086 facts-then-admission chain. NOT the wall itself:
   admitted structure comes from recorded verbatim alias text, spread
   presence is a syntax fact; spread VALUE semantics stay invented-structure.
2. Unannotated decls, no inference — 6 (defu.ts ×6). Blocker: inference of
   non-literal initializers beyond P076/P081-known positions — value facts
   the single pass refuses to invent.
3. Undeclared callback names — 3 (`merger` ×1, `currentValue` ×2). Blocker:
   call-callee resolution through enclosing parameter context (params carry
   no signature facts to user-call positions; P081 threaded params for the
   RECEIVER class, not for callee signatures).
4. Complex bodies — 2 (`isPlainObject`, `destr`). Blocker: control flow —
   out of subset by law.
5. Ambient overloads without bodies — 2 (`pLimit`, `limitFunction`).
   Blocker: ambient generic decls, triple-gated; P063 scope line stands.
6. Singletons — 3: `safeDestr` non-literal return (spread call value),
   `DefuFunction` cross-file named return, `namespace` unannotated param
   (whole-decl gate — P073 falsification preserved).

## Wall statement (M9 input)

The wall is not one thing: the ledger separates (a) buildable in-subset
chains the probes already pin — the Options/argument-object admission pair
(P085 facts, P086 admission), enclosing-param callee signatures (callbacks ×3),
ambient generic overloads (×2); from (b) declared impossible-without-breach —
type-operator evaluation (`Merger` ×3, `T` ×3 instantiation), control flow
(×2), value inference (×6), cross-file named returns + unannotated-param gate
(×3). M9 can spend primitives on (a) — each honest conversion re-measures (b)
without touching it. The 1/33 coverage number itself needs a prescan
admission, not a conversion: no remaining note implies a flipped construct,
and claiming otherwise would repeat the projection-as-verdict error M8 spent
three honest falsifications to close.
