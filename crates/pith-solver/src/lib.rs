//! Pith const/let-declaration solver: first real semantic thread.
//!
//! Pipeline: caller-supplied [`ConstDecl`]s (one per `const`/`let`
//! declarator) resolve their declaration spans scope-sensitively through the
//! [`Binder`], map their annotation names to [`TypeStore`] builtins, memoize
//! one [`QueryKind::TypeOf`] answer per declaration in the [`QueryDb`], and
//! emit [`PithDiagnostic`]s for contradictions. Diagnostics are sorted by
//! `(file, span.lo, span.hi)` so repeated runs agree byte-for-byte.
//!
//! Diagnostic code mapping (Pith verdict on the left, oracle on the right):
//!
//! - `PITH2322` <-> `TS2322`: initializer type is not assignable to the
//!   annotation type (primitive literal vs primitive annotation, wrong object
//!   member type, or primitive/object cross-shape). Message mirrors tsc shape:
//!   `Type 'string' is not assignable to type 'number'.`
//! - `PITH2304` <-> `TS2304`: annotation names an unknown type (primitive or
//!   object member). Message mirrors tsc shape:
//!   `Cannot find name 'Nope'.`
//! - `PITH2741` <-> `TS2741`: one object member is missing:
//!   `Property 'b' is missing in type '{ a: number; }' but required in type
//!   '{ a: number; b: string; }'.`
//! - `PITH2739` <-> `TS2739`: several object members are missing:
//!   `Type '{ a: number; }' is missing the following properties from type
//!   '{ a: number; b: string; c: boolean; }': b, c`
//! - `PITH2353` <-> `TS2353`: fresh object literal names an unknown member:
//!   `Object literal may only specify known properties, and 'b' does not
//!   exist in type '{ a: number; }'.`
//!
//! Object rules (P012, probed on tsc 7.0.2 `--strict`):
//!
//! - Members compare by name: annotation order drives the expected-type
//!   spelling and the missing-member list; literal order drives the
//!   actual-type spelling, wrong-member diagnostics, and first-excess pick.
//! - Fresh boolean members spell literally in actual types (`{ a: true; }`);
//!   every other kind widens (`number`, `string`, ...). `TS2322` messages
//!   always use widened names.
//! - One error family per declaration, priority wrong-member > excess >
//!   missing: any wrong member suppresses excess/missing; excess suppresses
//!   missing; two missing members collapse into one `TS2739`; only the first
//!   excess member is reported.
//! - Optional members (`y?: number`, P037) are known when present (wrong
//!   types diagnose exactly like required members) and invisible when
//!   absent: they never appear in missing lists, and expected-type
//!   elaborations spell them `y?: number | undefined`.
//! - `let` checks exactly like `const` (mutability/reassignment unchecked).
//!
//! Out-of-subset declarations (union annotations outside [`check_narrowing`],
//! missing annotations, non-literal or missing initializers, union/complex
//! member types, empty `{}` annotations, stale-literal excess candidates,
//! contradictory primitive/object initializer pairs) are recorded as
//! [`UnsupportedDecl`] entries, never silently dropped.
//!
//! BLOCKER (P004 adapter gap): [`ConstDecl::annotation`], [`ConstDecl::init`],
//! [`ConstDecl::init_object`], and [`ConstDecl::init_array`] are stand-ins
//! for the missing adapter facts
//! `DeclAnnotationFact` (annotation text + span), `InitLiteralFact`
//! (initializer literal kind + span), `ObjectMemberFact`s (member name +
//! literal kind per `{ ... }` entry), and array-element facts (literal kind
//! per `[ ... ]` entry). `ParsedFile` v1 carries declaration
//! spans plus (since P012) declarator scopes only, so no implementation can
//! recover these from facts alone without string-searching source text, which
//! is forbidden. The corpus driver hand-feeds them per fixture — the same
//! hand-fed seam as M1's `compute` closures — until the adapter emits them.
//! `let` declarators have no `DeclFact`s at all yet (`LetDeclFact` gap), so
//! the driver hand-feeds those whole. Declaration spans and scopes always
//! come from adapter facts; [`ConstDecl::span`] is only a fallback.
//!
//! Function declarations (P013): [`check_functions`] gates annotatedness
//! (every identifier parameter plus the return annotation) and body shape
//! (straight-line single `return`, the three P023 joins, and the P031
//! straight bodies only), then delegates each checkable position through
//! synthetic [`ConstDecl`]s to the same primitive/object paths, so
//! `TS2322`/`TS2304`/object-family verdicts match by construction.
//! Occurrence nodes for synthetic returns live in a disjoint range (see
//! `function_occurrence_node`), so consts and functions for one file may
//! share a [`QueryDb`]. Params, return annotations, and body shapes are
//! fact-fed from the adapter's function declarator facts; only the
//! literal-kind enum mapping is driver-side (mechanical and exhaustive).
//!
//! Straight-line joins (P023, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p023-probes/`):
//!
//! - `return "a"; return "b";` against `: number` reports two `TS2322`s, one
//!   per return; `return 1; return "b";` still reports the second and
//!   `return "a"; return 2;` the first only (unreachable returns still
//!   check). Each admitted return delegates through its own synthetic
//!   [`ConstDecl`] with its own occurrence node, so counts and first-line
//!   messages match by construction.
//! - `if/else` with a return in each branch reports per branch (one side
//!   wrong reports once; both wrong report twice).
//! - `if (c) return <e>; return <t>;` reports per position (a wrong guard
//!   return and a wrong tail return each report at their own line), for
//!   `typeof` guards and plain conditions alike — returns check
//!   independently of narrowing, so any condition qualifies.
//! - A non-literal position declines the whole declaration with a
//!   position-naming reason (never a partial verdict); loops,
//!   `else-if` chains, `if/else` plus a tail return, `throw`/bare
//!   branches outside admitted throw positions (P043), `continue`, and bare
//!   returns stay [`FunctionBody::Complex`]
//!   with the control-flow reason. `switch` bodies classify P040 (each
//!   `case` plus the optional `default` exactly one `return <expr>;`):
//!   fallthrough, complex cases, case-level declarations, non-literal
//!   discriminants or labels, and duplicate defaults decline with distinct
//!   recorded reasons instead. A missing `default` admits structurally
//!   (tsc's `TS2366` exhaustiveness error is a pinned gap — the subset has
//!   no declaration-completeness family). `try` bodies classify P039 (each arm
//!   exactly one `return <expr>;`, optional trailing return): `finally`
//!   clauses, destructured catch patterns, `throw` statements, and
//!   non-straight arms decline with distinct recorded reasons instead.
//!   A plain `catch (e)` admits structurally (the binding carries no
//!   facts); a used `return e` then rides the non-literal arm gate below.
//!
//! Straight-line multi-statement bodies (P031, probed on tsc 7.0.2
//! `--strict --pretty false`; probes in `.agent/scratch/p031-probes/`):
//!
//! - Leading `const`/`let` declarators plus a terminal literal `return`
//!   (at most four expanded items; multi-declarator statements expand per
//!   declarator) check per position through the same synthetic delegation:
//!   a wrong inner declarator and a wrong tail return each report at their
//!   own span, independently (`s3`: two `TS2322`s; `s1`/`s2` one each).
//!   Single-level blocks flatten when every inner statement is
//!   straight-line (`s6`, `t6`); a lone block holding the terminal return
//!   checks at the return span (`t1`).
//! - Unannotated cast-less leading declarators are skipped (tsc infers
//!   them — `t2` clean), as are nested `function` declarations (checked
//!   through their own facts — `u2` reports the inner return at its own
//!   span); `var`, destructured bindings, deeper nesting, non-terminal
//!   returns, and bodies past the item cap stay [`FunctionBody::Complex`].
//! - Identifier-initialized leading declarators decline per-position
//!   (pinned oracle-error divergence: `t3` spells `TS2322` where the
//!   subset has no value-type facts), and unannotated declined casts still
//!   diagnose `TS2352` at the operand span (`u3`). Inner object literals
//!   check through the object path (`t5`).
//!
//! Try/catch bodies (P039, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p039-probes/`):
//!
//! - `try { return 1; } catch { return 2; }` against `: number` is clean;
//!   a wrong `try` return and a wrong `catch` return each report one
//!   `TS2322` at their own position, and both wrong report twice — each
//!   arm checks independently through the same synthetic delegation as
//!   joins (no fixpoint, single pass). A trailing `return` after the
//!   `try` statement checks as another position (a wrong tail reports
//!   once; a wrong arm plus a wrong tail report twice).
//! - `finally` never suppresses: a wrong `try` return still reports with
//!   a clean `finally` return, and all-wrong `try`/`catch`/`finally`
//!   reports three times. The subset still declines every `finally`
//!   shape with its own reason (pinned divergence: the oracle checks,
//!   the solver records one note — never a forced verdict).
//! - A plain `catch (e)` admits structurally: an unused `e` changes no
//!   verdict (the binding carries no facts — oracle and solver both stay
//!   clean), while a used `return e` classifies `NonLiteral` and rides the
//!   existing position-naming decline in [`function_shape`] (whole-decl
//!   decline, 0 diagnostics, where tsc diagnoses `unknown`). Only
//!   destructured catch patterns decline at the frontend (no binding facts
//!   exist for patterns), as do `throw` statements in either arm (clean
//!   in tsc) and non-straight arms (multi-statement, bare returns). Each
//!   declines with a distinct reason.
//!
//! Switch bodies (P040, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p040-probes/`):
//!
//! - `switch (n) { case 1: return 1; case 2: return 2; default: return 3; }`
//!   against `: number` is clean; a wrong `case` return and a wrong
//!   `default` return each report one `TS2322` at their own position, and
//!   two wrong cases report twice — each position checks independently
//!   through the same synthetic delegation as joins (no fixpoint, single
//!   pass). String labels check the same way (`case "a":` positions
//!   diagnose identically — probed `n-string-disc`); a `default` in the
//!   middle and block-wrapped single returns (`case 1: { return 1; }`)
//!   are clean in tsc and admit the same way.
//! - Fallthrough (an empty `case` falling into the next clause), complex
//!   cases (extra statements before the return), case-level declarations
//!   (even with a literal tail return — `return x` over a case-local
//!   binding needs value-type facts), non-literal discriminants
//!   (`switch (tag())`), non-literal labels (`case tag():`), and duplicate
//!   defaults each decline with a distinct reason (pinned divergences: the
//!   oracle is clean on all but the duplicate, which spells `TS1113` — the
//!   solver records one note, never a forced verdict).
//! - A missing `default` admits structurally: all-clean cases stay silent
//!   where tsc reports `TS2366` (pinned oracle-error divergence — the
//!   subset has no declaration-completeness family). A `switch` paired with
//!   any other statement (e.g. a trailing `return`) stays
//!   [`FunctionBody::Complex`]: two paths, no join.
//!
//! Counted-`for` bodies (P041, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p041-probes/`):
//!
//! - `for (let i = 0; i < 3; i++) { return 1; } return 2;` against `: number`
//!   is clean; a wrong loop-body return reports one `TS2322` at its own
//!   position and a wrong tail one at the tail — each position checks
//!   independently through the same synthetic delegation as joins (no
//!   fixpoint, single pass). A provably zero-trip loop (`i < 0`) still
//!   reports its wrong body (trip counts are not modeled), and the braceless
//!   `for (...) return "oops";` anchors at the returned expression.
//! - Non-literal bounds (`i < n`), non-numeric bounds, non-idiom headers
//!   (`var`, multi-declarator, mismatched identifiers, non-`++` updates),
//!   non-`for` loops (`while`/`do`/`for-in`/`for-of`), infinite `for(;;)`,
//!   `break`/`continue` bodies (bare or labelled — labels are the only value
//!   either carries), and complex bodies each decline with a distinct reason
//!   (pinned divergences: the oracle checks every one of these shapes — the
//!   solver records one note, never a forced verdict).
//! - Loop-carried (cross-iteration) verdicts are an explicit pinned gap:
//!   positions check as if each runs once, so a `return i` over the loop
//!   variable rides the existing non-literal position gate (whole-decl
//!   decline, 0 diagnostics, where tsc types the value).
//!
//! Throw positions (P043, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p043-probes/`):
//!
//! - `throw` accepts any value: `throw new Error("x")` and `throw "s"` are
//!   both clean, so a throw position emits no verdict and carries no facts.
//!   A throw-only body is clean in tsc (no missing-return family under
//!   `--strict`), so it admits silently with zero positions.
//! - `if (c) throw ...; return <t>;` checks the tail exactly like the P023
//!   guard tail it mirrors (a wrong tail reports one `TS2322`; block-wrapped
//!   throws classify identically; any condition qualifies). The mirror
//!   (`if (c) return ...; throw ...;`) and `if/else` with a throw branch
//!   stay [`FunctionBody::Complex`] (both clean in tsc — pinned
//!   oracle-clean divergences, like the P039 `finally` decline).
//! - Straight bodies admit `throw` statements anywhere in the sequence:
//!   leading declarators and the terminal return check independently (a
//!   wrong inner and a wrong tail each report once), unreachable returns
//!   after a throw still check (the P023 precedent), and a terminal `throw`
//!   leaves no tail while leadings still check. Throws count toward the
//!   four-item cap (they are statements too).
//! - Throw inside otherwise-complex surroundings still declines whole-decl
//!   with a distinct reason: `throw` arms in `try`/`catch` (P039
//!   `TryUnsupported`), `throw` cases or defaults in `switch` (P040
//!   `SwitchUnsupported`), and any other multi-path body
//!   ([`FunctionBody::Complex`]) — never a partial verdict over the
//!   remaining positions.
//!
//! BLOCKER (P013 call facts), resolved by P014: call-site arity checking
//! runs on the adapter's `ParsedFile::calls` facts through [`check_calls`]. `void` returns are excluded from the
//! corpus: tsc accepts `undefined` for `void` while the shared annotation
//! map distinguishes them (pre-existing const-subset gap, unchanged here).
//!
//! Call-site checks (P014, probed on tsc 7.0.2 `--strict --pretty false`):
//!
//! - `PITH2554` <-> `TS2554`: `Expected 2 arguments, but got 1.` (arity is
//!   exact; tsc always spells `arguments`, even for one).
//! - `PITH2345` <-> `TS2345`: `Argument of type 'string' is not assignable
//!   to parameter of type 'number'.` (widened literal names, one per call).
//!
//! - One family per call site, arity first: `add("oops")` against two
//!   `number` params reports only `TS2554` (the type mismatch never
//!   surfaces), and `add("x", "y")` reports a single `TS2345` at the FIRST
//!   mismatched argument. The solver mirrors both.
//! - Span anchoring mirrors tsc: too-few arity anchors at the callee
//!   identifier, too-many at the first excess argument, arg-type at the
//!   mismatched argument — all from call facts, never string-searching.
//! - Range/variadic arities check (P037): optional/defaulted params admit a
//!   `min-max` range (`Expected 1-2 arguments, but got 3.`, still `TS2554`)
//!   while rest params admit `min`-or-more with `TS2555` below the minimum
//!   (`Expected at least 1 arguments, but got 0.`); fixed positions check
//!   exactly like exact-arity params and rest extras check against the `T`
//!   of the `...rest: T[]` element type (one `TS2345` at the first mismatch,
//!   same shape). Explicit `undefined` at an optional position is silent
//!   (its type carries `| undefined`); at fixed and rest positions it
//!   diagnoses like any other mismatch. Overload groups resolve by any-match
//!   (P044, below): the implementation signature never participates, and at
//!   most one diagnostic fires per call. Several same-name declarations with
//!   bodies (shadowing the fact set cannot disambiguate — a documented
//!   precision limit) still decline with reason.
//! - Still declined per site, each with its reason: required-after-optional
//!   shapes (`(a?: T, b: U)` — tsc itself errors the declaration with
//!   `TS1016` and checks calls at the exact total, both unmirrorable without
//!   declaration diagnostics), non-array rest types (`...rest: number` —
//!   tsc's `TS2370` at the declaration, likewise unmirrorable), and
//!   non-trailing rest markers (unprobed entirely).
//! - Unresolved callees are skipped, not diagnosed: the name is already
//!   tracked as an unresolved reference (see [`Binder::unresolved`]), so a
//!   diagnostic would double-report one signal (and per-site unsupported
//!   notes would flood the report with duplicates of a tracked signal).
//!   Return/body checkability is irrelevant: calls to complex-bodied
//!   functions still arity/arg-check, exactly like tsc.
//! - Non-literal arguments degrade per-argument (skipped for type checks,
//!   arity still enforced): expression facts do not exist yet, and declining
//!   whole calls over one identifier argument would forfeit decidable arity
//!   verdicts.
//!
//! Overload signatures (P044, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p044-probes/`):
//!
//! - `PITH2769` <-> `TS2769`: every arity-compatible signature fails on
//!   types: `No overload matches this call.` plus the continuation lines
//!   (`  The last overload gave the following error.` and the last
//!   signature's first `TS2345`-shaped mismatch, indented), anchored at the
//!   mismatched argument of the LAST signature in source order.
//! - `PITH2575` <-> `TS2575`: the count falls strictly between admitted
//!   ranges: `No overload expects 2 arguments, but overloads do exist that
//!   expect either 1 or 3 arguments.` (callee-anchored; the pair names the
//!   nearest distinct signature minimums below and above — ranges contribute
//!   their minimum).
//! - Resolution is any-match, order-independent: a call is clean when ANY
//!   signature admits it (a first-signature mismatch never surfaces when a
//!   later one matches, and vice versa). The implementation signature never
//!   participates (a call matching only the `...args: any[]` implementation
//!   still fails); `declare function` overloads and implementation-less
//!   groups resolve the same way (tsc's `TS2391` declaration diagnostic stays
//!   declined declaration-side — the subset spells no declaration
//!   diagnostics — while calls still check).
//! - Arity filters first, per signature: no compatible signature unions to
//!   `TS2554` (`Expected 1-2 arguments, but got 0.`, exact when the union is
//!   one count) at the callee for too-few and at `args[union-max]` for
//!   too-many, or `TS2555` below a rest minimum (`m16`) — all shared with the
//!   single-signature tail. Exactly one compatible signature checks exactly
//!   like a lone declaration (its own `TS2345` at the first mismatch).
//! - Generic signatures decline with a distinct reason (the oracle admits
//!   them — a pinned oracle-clean divergence), as do signatures with
//!   union/object/conditional/unknown parameter types (each with its own
//!   text-specific reason): exclusions that leave a matching signature stay
//!   clean (sound — the oracle checks a superset), but a call no checkable
//!   signature admits declines with every exclusion recorded, never a forced
//!   `TS2769` (the oracle might match an excluded signature or elaborate a
//!   different last signature).
//! - Assertion arguments pre-evaluate once per call: declined casts diagnose
//!   `TS2352` even when arity fails across overloads (`m15`), and matching
//!   uses the result kind (`m14`); complex casts skip per-argument, exactly
//!   like non-literals.
//!
//! Member calls on known values (P024, probed on tsc 7.0.2
//! `--strict --pretty false`; probes in `.agent/scratch/p024-probes/`)):
//! - The adapter emits member facts only for static member calls on a closed
//!   allowlist of known-value receivers (`JSON`, `Object`, `Array`,
//!   `console`, `Math`); everything else keeps the existing non-emission, so
//!   [`check_member_calls`] never verdicts a member call it has no
//!   probe-grounded signature for. No lib `.d.ts` modeling anywhere: known
//!   members carry opaque fixed-arity plus primitive-parameter signatures,
//!   and every other shape declines with a lib reason.
//! - Checked opaque signatures (each probed wrong-type, too-few, and
//!   too-many unless noted):
//!   - `Array.isArray(arg: any)`: exactly 1 argument; the parameter accepts
//!     every literal (probed `isArray(1)` and `isArray(null)` clean).
//!   - `Object.keys(o: object)`: exactly 1 argument; the `object` parameter
//!     is uncheckable in-subset, so argument checks skip per-argument while
//!     arity still enforces (literal `null`/`undefined` spell `TS2769` in
//!     tsc — pinned oracle-error divergence, never a forced `TS2345`).
//!   - `Math.floor/ceil/round/trunc/abs/sqrt/cbrt(x: number)` (exactly 1)
//!     and `Math.pow/atan2(x: number, y: number)` (exactly 2): full
//!     arity-plus-`TS2345` checking, exactly like direct calls.
//! - Known members with uncheckable shapes decline per site with lib reasons
//!   (never a forced verdict): `JSON.parse` takes a range of arities
//!   (`Expected 1-2 arguments, but got 0.` in tsc) plus a function-typed
//!   reviver; `JSON.stringify` is overloaded (`TS2769` in tsc);
//!   `console.warn/log/error` and `Math.max/min` are variadic (the rest-arg
//!   precedent). The destr `JSON.parse(value)` and `console.warn(...)` sites
//!   land here: recorded, never silent, never mis-verdicted.
//! - Unknown members on known receivers (`JSON.nope`) decline with a lib
//!   reason (tsc spells `TS2339` — pinned oracle-error divergence); unknown
//!   receivers consult the unresolved gate exactly like direct calls (tracked
//!   names skip silently with tsc's `TS2304` pinned; untracked names decline
//!   as driver skew, never silently dropped).
//! - One family per site, same anchoring law as direct calls (too-few at the
//!   member identifier, too-many at the first excess argument, arg-type at
//!   the mismatched argument) — all spans from member facts, never
//!   string-searching. A locally declared binding shadowing a known value
//!   still routes opaque (documented limit: member facts carry no occurrence
//!   scope, so shadowing is indistinguishable facts-side).
//!
//! Range arities and optional members (P037, probed on tsc 7.0.2
//! `--strict --pretty false`; probes in `.agent/scratch/p037-probes/`):
//!
//! - `function f(a: number, b?: number)` and `function g(a: number, b: number
//!   = 2)` both admit 1-2 arguments silently and diagnose both sides with
//!   the range spelling (`Expected 1-2 arguments, but got 0.` / `... but got
//!   3.`, still `TS2554`): anchoring follows the exact-arity law (too-few at
//!   the callee, too-many at the first excess argument). All-optional lists
//!   spell `Expected 0-1 arguments, but got 2.` the same way.
//! - `function h(a: number, ...rest: number[])` admits 1-or-more silently;
//!   zero arguments diagnose `TS2555` (`Expected at least 1 arguments, but
//!   got 0.`, callee-anchored) while extras check against the element type
//!   (`h(1, "oops")` reports `TS2345` at the argument, exactly the fixed
//!   shape). A zero-fixed rest list admits zero arguments. Non-array rest
//!   types error the declaration in tsc (`TS2370: A rest parameter must be of
//!   an array type.`) with tuple-typed call fallout the subset cannot spell,
//!   so calls against them decline.
//! - In-range wrong types diagnose positionally (`o1(1, "oops")` and
//!   `o1("oops", 2)` each report `TS2345` at their own argument), except
//!   explicit `undefined` at an optional position, which is silent (the
//!   parameter's type carries `| undefined`); the same `undefined` at a
//!   fixed or rest position diagnoses normally.
//! - Required-after-optional (`(a?: T, b: U)`, and defaulted-then-required
//!   `(a: T = …, b: U)`) errors the declaration in tsc (`TS1016: A required
//!   parameter cannot follow an optional parameter.`) and checks calls at
//!   the exact total (`Expected 2 arguments …`); the subset has no
//!   declaration-diagnostic family, so these decline per site with a reason.
//! - Optional object members (`{ x: number; y?: number }`,
//!   `interface P { x: number; y?: number }`): absent uses stay silent,
//!   present uses check exactly like required members (wrong types diagnose
//!   `TS2322` with the plain member type), and missing calculations skip
//!   them — `{}` against `{ x: number; y?: number }` reports only `x`, and
//!   `[1]` against either spelling reports only `x` (`TS2741` in both).
//!   Expected-type elaborations spell the marker verbatim (`{ x: number; y?:
//!   number | undefined; }` for inline annotations; the bare interface name
//!   otherwise), so excess members name the same text tsc does.
//!
//! `any`/`unknown` boundary plus `as` casts (P025, probed on tsc 7.0.2
//! `--strict --pretty false`; probes in `.agent/scratch/p025-probes/`):
//!
//! - `any` annotations admit every value: `const m: any = 1`, `takeAny("oops")`
//!   against `(x: any)`, `function f(x: any): any { return 1; }`, and
//!   `const a: number = av` (an `any`-typed source) are all clean — both
//!   directions silent. The solver mirrors with silence (never a forced
//!   `PITH2304`: `any` is a known annotation now).
//! - `unknown` annotations admit every bearing value (`const u: unknown = "s"`
//!   clean); `unknown`-typed VALUES against `T` diagnose `TS2322`
//!   (`Type 'unknown' is not assignable to type 'string'.`), which the solver
//!   reaches through admitted `as unknown` casts. Identifier-held `unknown`
//!   (`const a: string = uv`) declines: the subset has no value-type facts.
//! - `never` annotations diagnose `TS2322` for every bearing literal
//!   (`Type 'number' is not assignable to type 'never'.`); `never` parameters
//!   decline (unprobed message shape — never forced).
//! - `as` / angle assertions admit on overlap and decline with `TS2352`
//!   (`Conversion of type 'string' to type 'number' may be a mistake because
//!   neither type sufficiently overlaps with the other. If this was
//!   intentional, convert the expression to 'unknown' first.`). In-subset
//!   overlap: same widened primitive, or either side `any` / `unknown` /
//!   `never` (`true as boolean`, `1 as any`, `"x" as unknown`, `"x" as never`,
//!   `uv as string` all admit; `string as number`, `null as undefined`,
//!   `"x" as { a: number; }` decline). Angle assertions share the rule.
//! - `satisfies` admits on the same overlap but stays transparent to the
//!   OPERAND type; its decline spells `TS1360`
//!   (`Type 'string' does not satisfy the expected type 'number'.`).
//! - Declined casts diagnose INDEPENDENTLY of the annotation: `const s:
//!   string = ("hello" as number)` reports BOTH `TS2322` and `TS2352`, and
//!   `const m: any = ("hello" as number)` reports `TS2352` alone; the solver
//!   emits the cast diagnostic then continues through the existing path with
//!   the result kind (`as`/angle: the target; `satisfies`: the operand).
//!   Unannotated declined casts still diagnose (`const g = "x" satisfies
//!   number` spells `TS1360`).
//! - Complex casts (non-literal operands, `None`/union/object/literal
//!   targets, parenthesized chains past the outermost) decline the whole
//!   declaration with a reason — never a forced `TS2352` (object targets
//!   cannot spell canonically from sliced text). Identifier-held `unknown`
//!   (`const a: string = uv`) declines in [`check_one`] for the same
//!   reason: no value-type facts. The P033 narrowing path
//!   ([`check_narrowing`]) checks that shape through unknown targets instead
//!   — see the narrowing probe record.
//! - Contract divergence (falsified premise, disclosed): the P025 contract
//!   expected explicit `any`-to-`T` flows to diagnose, but the oracle is
//!   silent on every such flow (probes `b`, `h`, `j`). The solver mirrors
//!   the oracle (silence), not the contract premise.
//!
//! Classes (P020, probed on tsc 7.0.2 `--strict --pretty false`; probes in
//! `.agent/scratch/p020-probes/`):
//!
//! - Property initializers check exactly like consts: `x: number = "oops"`
//!   diagnoses `TS2322: Type 'string' is not assignable to type 'number'.`
//!   at the property. Properties carry no binder identity, so synthetic
//!   declarations use dotted `Class.prop` names that can never resolve and
//!   always fall back to the fact span (which is also the oracle anchor).
//! - `new` checks exactly like calls through the same [`check_one_call`]
//!   path: too-few `TS2554` at the callee (`Expected 2 arguments, but got
//!   1.`), too-many at the first excess argument, wrong argument types
//!   `TS2345` at the argument. Classes without a constructor take 0
//!   arguments (`Expected 0 arguments, but got 1.`); constructor parameter
//!   properties (`private x: number`) check normally; optional/rest
//!   constructor params check per site exactly like function calls (ranges,
//!   `TS2555` minima, and rest-element checks all flow through the shared
//!   [`check_one_call`] path). Decline reasons say
//!   "call" for `new` sites (documented wording fold — tsc itself spells
//!   `arguments` for both).
//! - Declines (each probed): method bodies (`TS2322` at the return in tsc),
//!   accessors (same), heritage (`extends` clean in tsc; `implements`
//!   mismatches spell the new family `TS2416`), statics (static-prop
//!   mismatches spell `TS2322`), computed keys (`TS2322`), class
//!   expressions (`TS2322`), abstract/declare classes (clean in tsc),
//!   generic classes, missing initializers (`TS2564` under `--strict`),
//!   and `this`-assignments (clean in tsc — they satisfy definite
//!   assignment, which needs flow facts the subset refuses).
//! - Rationale for class-level (not per-method) decline notes: one note per
//!   out-of-subset family per class keeps reports proportional to
//!   declarations — per-method notes would multiply on every realistic
//!   class — while spans stay precise at the class level (the P016
//!   generic-decl precedent: one declaration note covers all its uses).
//!   Only genuinely per-property shapes (`declare`/abstract/decorated
//!   properties) decline per-property, mirroring interface members.
//!
//! Interface-typed consts (P017, probed on tsc 7.0.2
//! `--strict --pretty false`):
//!
//! - Member checks reuse the object path, so families match: wrong members
//!   diagnose per-member `TS2322` (`Type 'string' is not assignable to type
//!   'number'.`), one missing member `TS2741`, several `TS2739`, first
//!   excess `TS2353` — with the wrong > excess > missing priority intact.
//! - Missing/excess/cross-shape elaborations spell the INTERFACE NAME, never
//!   expanded members: `Property 'label' is missing in type '{ x: number; }'
//!   but required in type 'Point'.`, `... 'extra' does not exist in type
//!   'Point'.`, `Type 'number' is not assignable to type 'Point'.`
//! - `readonly` needs no special case: assignability ignores it (clean when
//!   members match, plain `TS2322` when wrong).
//! - Heritage clauses, generic parameter lists, methods, index/call/
//!   construct signatures, computed or non-identifier keys, and missing
//!   annotations decline with per-member reasons (pinned oracle-clean
//!   divergences: tsc checks all of these). Optional members check instead:
//!   absent uses stay silent while present ones run the shared comparison
//!   (P037).
//! - Merged pairs (`interface Foo {}` + `const Foo = …`) share one
//!   [`SymbolId`]: oxc pre-merges same-scope redeclarations (so the
//!   frontend emits one fact), and the P005 binder law covers any residual
//!   split — annotation names resolve through the [`Binder`] exactly like
//!   values, so both meanings stay reachable and diagnostics anchor at the
//!   first-declaration span.
//!
//! [`check_interfaces`] resolves each non-primitive, non-union annotation
//! through the [`Binder`] to an [`InterfaceShape`] (driver-mapped from the
//! adapter's interface facts) and runs the shared object comparison with
//! the interface name as the expected-type spelling — a thin wrapper, no
//! duplicated verdict logic. Unknown names diagnose `PITH2304` exactly like
//! [`check_one`]; names that resolve to a symbol no shape claims decline
//! (type aliases, classes, and driver skew are all non-interface targets —
//! recorded, never verdict).
//!
//! Enums as types (P018, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p018-probes/`):
//!
//! - Numeric literals check by VALUE against the enum's numeric members:
//!   `const a: Color = 1` is clean when a member holds `1`, while `5`
//!   diagnoses `TS2322: Type '5' is not assignable to type 'Color'.`
//!   (literal-type spelling, values not source text: `0x2` against
//!   `{ A = 0, B = 1 }` spells `Type '2'`; `1.0` matches `1`).
//! - String literals NEVER match, even member values: `const g: Str = "a"`
//!   diagnoses `TS2322: Type '"a"' is not assignable to type 'Str'.`
//!   (double-quote spelling — fixtures stay double-quoted). Booleans spell
//!   literally (`Type 'true'`); `null`/`undefined` spell widened.
//! - Member accesses (`Color.Red`, `Color["Red"]`) are clean in tsc but
//!   inexpressible without expression facts: non-literal initializers
//!   decline (the largest pinned oracle-clean divergence here).
//! - Object literals diagnose compositionally (`Type '{}' is not assignable
//!   to type 'Color'.`); missing initializers decline with the usual reason.
//! - `const enum` behaves identically (probed: `0` clean, `7` errors) —
//!   noted, never forked. Ambient (`declare`) enums accept every literal in
//!   tsc, so the solver declines them (pinned oracle-clean divergence).
//! - Computed members (identifiers, `-1`, calls, cross-references like
//!   `B = A`) decline the whole enum: tsc folds computed values in, which
//!   needs const-eval the subset refuses. Auto-increment past numeric
//!   literals is facts; anything else unknowable declines at the member.
//!
//! Namespaces as scope containers (P018, probed on tsc 7.0.2):
//!
//! - Qualified annotations resolve through binder scopes: `NS.Dir` checks
//!   like `Dir` but spells the SHORT name (`Type '9' is not assignable to
//!   type 'Dir'.`); `NS.Point` runs the interface path spelling `Point`
//!   (`TS2741`/`TS2353`/`TS2322` families intact, wrong > excess >
//!   missing). The display rule is uniform: the annotation minus its leading
//!   namespace qualification (`NS.Dir.Up` spells `Dir.Up`, `Color.Red`
//!   spells `Color.Red` — each probed).
//! - Missing AND non-exported members both diagnose `TS2694: Namespace 'NS'
//!   has no exported member 'Nope'.` (the qualifier names the full resolved
//!   prefix: `NS.Dir.Nope` spells `Namespace 'NS.Dir'`, `Color.Nope` spells
//!   `Namespace 'Color'` — each probed). Export visibility is facts
//!   (`exported`, plus `exported_members` for values), except inside ambient
//!   namespaces where every member shows (probed tsc 7.0.2).
//! - A bare namespace as a type diagnoses `TS2709: Cannot use namespace 'NS'
//!   as a type.` — single-name only (probed, even for value-only
//!   namespaces). A TRAILING namespace in a qualified path instead diagnoses
//!   `TS2749: 'WithTypes.Inner' refers to a value, but is being used as a
//!   type here. Did you mean 'typeof WithTypes.Inner'?` (probed: the rule is
//!   positional, so the solver mirrors each position exactly).
//! - Qualifying past an interface diagnoses `TS2713: Cannot access 'Point.X'
//!   because 'Point' is a type, but not a namespace. …` (probed; mirrored
//!   for one leftover segment, deeper leftovers decline).
//! - Exported non-type members (`NS.VAL` as a type) error `TS2749` in tsc,
//!   but the subset cannot tell values from type aliases without value
//!   facts, so they decline instead (pinned divergence — never a wrong
//!   `TS2694`, which would claim the member is hidden). Trailing
//!   NAMESPACES still mirror `TS2749`: their identity is a shape fact, so
//!   no confusion is possible.
//! - An unresolvable head already tracked as an unresolved reference skips
//!   silently (the [`check_calls`] precedent: tracked once, never
//!   double-diagnosed — tsc's `TS2503` is the folded differential).
//! - Value positions (`NS.VAL` initializers, `NS.Dir.Up` uses) are clean in
//!   tsc but inexpressible without expression facts: non-literal declines
//!   (pinned oracle-clean divergences).
//!
//! [`check_enums`] routes each declaration: `{...}`/primitive/union
//! spellings delegate to [`check_one`] unchanged; other names resolve to
//! enum/interface shapes (single or namespace-qualified) and run the shared
//! object/enum comparisons with the short-name spelling. Enum declarations
//! skip the [`QueryDb`] memo (no [`TypeData`](pith_types::TypeData) shape
//! exists for enums — the union precedent); interface/plain paths memoize
//! exactly like before.
//!
//! Local type aliases (P038, probed on tsc 7.0.2 `--strict --pretty false`;
//! probes in `.agent/scratch/p038-probes/`):
//!
//! - Single-level expansion only, mirroring the P035 imported-alias rules:
//!   alias-to-primitive/boundary rewrites the annotation to the target
//!   spelling and checks exactly as if written (`Num = number`: clean uses
//!   stay silent, `"oops"` diagnoses `TS2322` spelling `number`);
//!   alias-to-interface/enum relinks the underlying shape and checks through
//!   the existing shape paths with the UNDERLYING name as the display text
//!   (alias transparency: missing members spell `required in type 'Point'`,
//!   excess spells `does not exist in type 'Point'`, enum values spell
//!   `type 'Color'` — each probed, unlike the P035 multifile pinned
//!   divergence, which spells the alias).
//! - Declines, each with a distinct reason, never a forced verdict:
//!   chained (alias-to-alias; tsc resolves transitively — pinned divergence),
//!   generic (`has_type_params`, bare or `Box<number>`-head uses), circular
//!   (self-targets; tsc's `TS2456` at the declaration is the pinned gap),
//!   complex/non-identifier targets (unions, object literals, `T<K>` spells),
//!   unclaimed targets (no interface, enum, or primitive owns the name), and
//!   duplicate same-name aliases (tsc's `TS2300` is the pinned gap).
//! - Shadowing: a local const bearing the alias name wins — the use declines
//!   instead of expanding, so an expansion can never hijack a value binding
//!   (multifile `has_local_const` precedent). tsc checks the type meaning
//!   there, so top-level shadowing is a pinned oracle-clean divergence;
//!   same-name interface/enum shapes win automatically (the binder merges
//!   same-scope redeclarations, so the shape claim fires first — probed: the
//!   use still checks as the interface alongside tsc's `TS2300`s).
//! - Entry coverage: [`check_enums_with_aliases`] relinks shapes;
//!   [`check_file_with_aliases`] rewrites primitives but declines
//!   named-shape targets — it holds no shape tables — with an entry-point
//!   reason. The base [`check_file`]/[`check_enums`] entries thread empty
//!   tables and keep today's verdicts, as does [`multifile`] (which keeps
//!   its own import-alias rules and never calls the variants — a pinned
//!   gap: multifile-local aliases keep today's declines). Qualified
//!   (`NS.Alias`), union-member, narrowing, function-return, class, and
//!   legacy-interface-entry sites keep today's verdicts (pinned gaps: those
//!   paths thread an empty scope).
//! - Flips (P037 discipline): annotations naming a local alias no longer
//!   diagnose `PITH2304` — primitives/boundaries check, the rest decline
//!   with reasons. No existing corpus fixture declares an alias, so no
//!   baseline moves.
//!
//! Lib types, first cut (P034, probed on tsc 7.0.2
//! `--strict --pretty false`; probes in `.agent/scratch/p034-probes/`):
//!
//! - `Array<T>` and `T[]` admit single primitive or boundary (`any`/
//!   `unknown`/`never`) element types. Array-literal members verify one by
//!   one through the existing literal machinery: each mismatched member
//!   diagnoses `TS2322` (`Type 'string' is not assignable to type 'number'.`,
//!   one per member in literal order), non-literal members skip silently
//!   (probed clean — the call-argument precedent), and `any`/`unknown`
//!   elements admit everything. Expected types always spell the suffix form
//!   (`Type 'number' is not assignable to type 'number[]'.`, even when the
//!   annotation reads `Array<number>`).
//! - `Promise<T>` admits async function returns carrying literal values:
//!   the annotation unwraps to `T` (or to `U[]` for `Promise<Array<U>>`,
//!   which then checks member-wise) and the return checks through the
//!   existing paths. `await` is transparent in tsc (`return await "oops"`
//!   diagnoses exactly like `return "oops"`); the adapter classifies `await`
//!   as non-literal, so awaited kinds ride the hand-fed seam (see below).
//!   Non-async `Promise` returns decline (tsc spells `TS2322`/`TS2739` the
//!   subset cannot spell — never forced), as do `Promise<never>` (literal
//!   spellings need value facts) and bare/multi-arg `Promise`/`Array`
//!   (tsc `TS2314`).
//! - Every other lib shape declines with a distinct reason, never a forced
//!   `TS2304`: tuples (`[number, string]` — tuples are NOT arrays),
//!   `readonly` arrays, utility types (`Record`, `Partial`, ...),
//!   collections (`Map`, `Set`, ...), iterables, typed arrays, and DOM types.
//!   Cross-shapes diagnose where tsc's spelling is facts-expressible:
//!   array inits against primitive/`never` annotations spell the actual
//!   (`number[]`, `never[]` for empty, `unknown` for `as unknown` results);
//!   mixed-kind arrays spell unions in tsc (`(string | number)[]`), so they
//!   decline instead of mis-spelling. Array inits against object/interface
//!   annotations spell the oracle's `TS2741`/`TS2739` missing family with
//!   the array spelling as the actual type.
//!
//! BLOCKER (P004 adapter gap, same seam as [`ObjectInit`]): [`ArrayInit`]
//! members, [`FunctionDecl::is_async`], and awaited return kinds are
//! hand-fed per fixture — the adapter emits no array-member facts, no async
//! flag, and classifies `await` as non-literal. Spans/scopes/identities
//! always come from adapter facts; only shapes ride the seam.
//!
//! Design law (H-002): literal freshness and every other per-occurrence
//! verdict lives in query-side tables keyed by occurrence
//! ([`NodeId`], see [`FreshnessTable`] plus the [`QueryDb`] memo entries),
//! never in [`TypeData`](pith_types::TypeData). Shared structure (member
//! names, builtin [`TypeId`]s) is canonical and global; freshness is local.

use std::collections::HashMap;

use pith_ids::{FileId, NodeId, Span, SymbolId, TypeId};
use pith_queries::{Dep, QueryDb, QueryKey, QueryKind};
use pith_symbols::Binder;
use pith_types::{TypeData, TypeStore};

/// Multi-file programs: import graphs, cross-file checking, invalidation.
pub mod multifile;

/// Code for literal-vs-annotation contradictions (oracle `TS2322`).
pub const CODE_MISMATCH: &str = "PITH2322";
/// Code for unknown annotation names (oracle `TS2304`).
pub const CODE_UNKNOWN_ANNOTATION: &str = "PITH2304";
/// Code for one missing object member (oracle `TS2741`).
pub const CODE_MISSING_MEMBER: &str = "PITH2741";
/// Code for several missing object members (oracle `TS2739`).
pub const CODE_MISSING_MANY: &str = "PITH2739";
/// Code for excess members in a fresh object literal (oracle `TS2353`).
pub const CODE_EXCESS_MEMBER: &str = "PITH2353";
/// Code for call-site arity mismatches (oracle `TS2554`).
pub const CODE_ARITY: &str = "PITH2554";
/// Code for rest-minimum arity mismatches (oracle `TS2555`).
pub const CODE_ARITY_MIN: &str = "PITH2555";
/// Code for call-site argument-type mismatches (oracle `TS2345`).
pub const CODE_ARG_TYPE: &str = "PITH2345";
/// Code for overload calls matching no signature (oracle `TS2769`).
pub const CODE_OVERLOAD: &str = "PITH2769";
/// Code for overload calls with an admitted-by-none count inside the span
/// of ranges (oracle `TS2575`).
pub const CODE_OVERLOAD_ARITY: &str = "PITH2575";
/// Code for declined `as`/angle assertions (oracle `TS2352`).
pub const CODE_CAST: &str = "PITH2352";
/// Code for declined `satisfies` assertions (oracle `TS1360`).
pub const CODE_SATISFIES: &str = "PITH1360";
/// Code for namespace member misses (oracle `TS2694`).
pub const CODE_NO_EXPORTED_MEMBER: &str = "PITH2694";
/// Code for namespaces used as types (oracle `TS2709`).
pub const CODE_NAMESPACE_AS_TYPE: &str = "PITH2709";
/// Code for values used as types (oracle `TS2749`).
pub const CODE_VALUE_AS_TYPE: &str = "PITH2749";
/// Code for qualifying past a type (oracle `TS2713`).
pub const CODE_TYPE_NOT_NAMESPACE: &str = "PITH2713";

/// One solver verdict: machine-comparable code plus anchored span.
///
/// `file`/`span` always name a declaration span (never a string slice);
/// `message` mirrors the oracle wording for its code family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PithDiagnostic {
    /// `"PITH2322"`-style code; see [`CODE_MISMATCH`]/[`CODE_UNKNOWN_ANNOTATION`].
    pub code: String,
    /// File owning the diagnostic span.
    pub file: FileId,
    /// Declaration span the diagnostic points at.
    pub span: Span,
    /// Human wording, mirroring the oracle message for the code family.
    pub message: String,
}

/// A declaration the solver refuses to verdict, with the reason why.
///
/// Out-of-subset input lands here so it is recorded, never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsupportedDecl {
    /// File owning the declaration.
    pub file: FileId,
    /// Declaration span (binder span when bound, caller span otherwise).
    pub span: Span,
    /// Why no verdict exists (e.g. `"union annotation 'number | string'"`).
    pub reason: String,
}

/// Full per-file verdict: sorted errors plus sorted unsupported notes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FileReport {
    /// Error diagnostics, sorted by `(file, span.lo, span.hi)`.
    pub diagnostics: Vec<PithDiagnostic>,
    /// Out-of-subset notes, sorted by `(file, span.lo, span.hi)`.
    pub unsupported: Vec<UnsupportedDecl>,
}

/// Initializer shapes inside the solver subset.
///
/// Only primitive literals are classifiable. Anything else needs expression
/// facts the adapter does not emit yet, so it maps to [`InitKind::NonLiteral`]
/// and becomes an [`UnsupportedDecl`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitKind {
    /// A numeric literal (`1`, `0x10`, ...).
    Number,
    /// A string literal (`"ok"`, ...).
    String,
    /// `true` / `false`.
    Boolean,
    /// `null`.
    Null,
    /// `undefined`.
    Undefined,
    /// An admitted `as unknown` result (never a direct literal: only
    /// [`evaluate_cast`] produces it). Spells `unknown` in messages, so
    /// `unknown`-into-`T` flows diagnose exactly like the oracle.
    Unknown,
    /// Any non-literal initializer (identifier, object, call, ...).
    NonLiteral,
}

impl InitKind {
    /// The builtin [`TypeId`] this literal inhabits.
    ///
    /// `NonLiteral` has no known type here, so it yields [`TypeStore::UNKNOWN`]
    /// and callers must route it to unsupported, never to a verdict.
    #[must_use]
    pub fn type_id(self) -> TypeId {
        match self {
            Self::Number => TypeStore::NUMBER,
            Self::String => TypeStore::STRING,
            Self::Boolean => TypeStore::BOOLEAN,
            Self::Null => TypeStore::NULL,
            Self::Undefined => TypeStore::UNDEFINED,
            Self::Unknown | Self::NonLiteral => TypeStore::UNKNOWN,
        }
    }

    /// The tsc-style type name used in diagnostic messages.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Number => "number",
            Self::String => "string",
            Self::Boolean => "boolean",
            Self::Null => "null",
            Self::Undefined => "undefined",
            Self::Unknown | Self::NonLiteral => "unknown",
        }
    }
}

/// Whether the declarator is `const`, `let`, or a synthetic function return.
///
/// All three check identically today: mutability and reassignment are
/// unchecked (no flow analysis yet), and function returns delegate through
/// synthetic declarations (see [`check_functions`]). The kind is recorded so
/// a later phase can diverge narrowing without re-plumbing every input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclKind {
    /// A `const` declarator.
    Const,
    /// A `let` declarator (same rules as [`DeclKind::Const`] for now).
    Let,
    /// A synthetic function-return declaration (same rules as
    /// [`DeclKind::Const`] for now; never constructed by const drivers).
    Function,
}

/// One member of a hand-fed object-literal initializer.
///
/// The boolean payload exists for exactly one reason: tsc spells fresh
/// boolean members literally (`{ a: true; }`) in missing-member
/// elaborations while every other kind widens (`number`, `string`, ...), so
/// the verdict needs the value (probed on tsc 7.0.2, P012).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectMemberKind {
    /// A numeric literal member.
    Number,
    /// A string literal member.
    String,
    /// A boolean literal member (payload is the literal value).
    Boolean(bool),
    /// A `null` member.
    Null,
    /// An `undefined` member.
    Undefined,
    /// Any non-primitive member init (identifier, call, nested object, ...):
    /// expression facts the adapter does not emit yet.
    NonLiteral,
}

impl ObjectMemberKind {
    /// Widened tsc name, used in `TS2322`-family messages.
    #[must_use]
    pub fn widened_name(self) -> &'static str {
        match self {
            Self::Number => "number",
            Self::String => "string",
            Self::Boolean(_) => "boolean",
            Self::Null => "null",
            Self::Undefined => "undefined",
            Self::NonLiteral => "unknown",
        }
    }

    /// Member spelling inside `{ ... }` elaboration types (`TS2741`/`TS2739`
    /// actual types keep fresh boolean literals literally).
    #[must_use]
    pub fn display_name(self) -> &'static str {
        match self {
            Self::Boolean(true) => "true",
            Self::Boolean(false) => "false",
            Self::Number | Self::String | Self::Null | Self::Undefined => self.widened_name(),
            Self::NonLiteral => "unknown",
        }
    }

    /// The builtin [`TypeId`] this member literal inhabits.
    ///
    /// `NonLiteral` has no known type here, so it yields
    /// [`TypeStore::UNKNOWN`] and callers must route it to unsupported,
    /// never to a verdict.
    #[must_use]
    pub fn type_id(self) -> TypeId {
        match self {
            Self::Number => TypeStore::NUMBER,
            Self::String => TypeStore::STRING,
            Self::Boolean(_) => TypeStore::BOOLEAN,
            Self::Null => TypeStore::NULL,
            Self::Undefined => TypeStore::UNDEFINED,
            Self::NonLiteral => TypeStore::UNKNOWN,
        }
    }
}

/// One `{ ... }` entry: its name plus its literal kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectMemberInit {
    /// Member name as written in the literal.
    pub name: String,
    /// Literal kind of the member value.
    pub kind: ObjectMemberKind,
}

/// Hand-fed object-literal initializer facts for one declaration.
///
/// `members` is literal source order. `fresh` says the occurrence is a
/// direct syntactic literal (always true for adapter-realizable inputs —
/// only direct literals will ever carry member facts); `false` pins the
/// stale-literal gate in tests, where excess candidates must stay
/// [`UnsupportedDecl`]s instead of diagnosing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObjectInit {
    /// Member facts in literal source order.
    pub members: Vec<ObjectMemberInit>,
    /// Whether this occurrence is a fresh (direct) literal.
    pub fresh: bool,
}

/// Hand-fed array-literal initializer facts for one declaration.
///
/// `members` holds one [`ArrayMemberKind`] per element in literal source
/// order. Unlike [`ObjectInit`] there is no freshness flag: arrays have no
/// excess-property checks, so every literal occurrence checks member-wise
/// identically.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArrayInit {
    /// Element facts in literal source order.
    pub members: Vec<ArrayMemberKind>,
}

/// One array-literal element: its literal kind.
///
/// Deliberately payload-free (mirroring the call-argument precedent): tsc's
/// array diagnostics always spell widened names (`Type 'string' is not
/// assignable to type 'number'.`, probed 7.0.2), so no boolean value rides
/// along. Anything expression-shaped is [`ArrayMemberKind::NonLiteral`]:
/// those elements skip silently (probed clean), exactly like non-literal
/// call arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArrayMemberKind {
    /// A numeric literal element.
    Number,
    /// A string literal element.
    String,
    /// A `true` / `false` element.
    Boolean,
    /// A `null` element.
    Null,
    /// An `undefined` element.
    Undefined,
    /// Any non-literal element (identifier, spread, call, ...): skipped,
    /// never verdict.
    NonLiteral,
}

impl ArrayMemberKind {
    /// Widened tsc name, used in `TS2322`-family messages.
    #[must_use]
    pub fn widened_name(self) -> &'static str {
        match self {
            Self::Number => "number",
            Self::String => "string",
            Self::Boolean => "boolean",
            Self::Null => "null",
            Self::Undefined => "undefined",
            Self::NonLiteral => "unknown",
        }
    }

    /// The builtin [`TypeId`] this element literal inhabits.
    ///
    /// `NonLiteral` has no known type here, so it yields
    /// [`TypeStore::UNKNOWN`]; callers skip those elements, never verdict
    /// them.
    #[must_use]
    pub fn type_id(self) -> TypeId {
        match self {
            Self::Number => TypeStore::NUMBER,
            Self::String => TypeStore::STRING,
            Self::Boolean => TypeStore::BOOLEAN,
            Self::Null => TypeStore::NULL,
            Self::Undefined => TypeStore::UNDEFINED,
            Self::NonLiteral => TypeStore::UNKNOWN,
        }
    }
}

/// One `const`/`let` declarator to check.
///
/// `annotation`/`init`/`init_object` are hand-fed stand-ins for the missing
/// adapter facts (see the module-level BLOCKER); `scope`/`symbol`/`span`
/// locate the declaration span, preferring facts over fallbacks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstDecl {
    /// Declared name, resolved scope-sensitively through the [`Binder`].
    pub name: String,
    /// Fallback span, used only when neither `symbol` nor scope-sensitive
    /// resolution finds the declaration in the [`Binder`].
    pub span: Span,
    /// Per-file scope index of the declarator (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity when the driver resolved it (preferred over
    /// scope-sensitive lookup); must come from the same `file`/`Binder`.
    pub symbol: Option<SymbolId>,
    /// `const` vs `let` vs synthetic function return; same checking rules
    /// (mutability unchecked).
    pub kind: DeclKind,
    /// Raw annotation text (`Some("number")`, `Some("{ a: number }")`);
    /// `None` means unannotated.
    pub annotation: Option<String>,
    /// Initializer literal kind; `None` means no initializer.
    pub init: Option<InitKind>,
    /// Object-literal members when the initializer is `{ ... }`; `None`
    /// otherwise. A `Some` paired with a primitive `init` (or vice versa)
    /// is contradictory input and becomes an [`UnsupportedDecl`].
    pub init_object: Option<ObjectInit>,
    /// Array-literal members when the initializer is `[ ... ]`; `None`
    /// otherwise. Pairs with any other initializer shape (`init`,
    /// `init_object`, `cast`) the same contradictory way, and becomes an
    /// [`UnsupportedDecl`].
    pub init_array: Option<ArrayInit>,
    /// Outermost assertion facts when the initializer is an `as` /
    /// `satisfies` / angle assertion (`None` otherwise). Driver-mapped
    /// from the adapter's cast facts; [`check_one`] evaluates the
    /// admit/decline rule and checks the result through the existing path.
    pub cast: Option<CastInput>,
}

/// One function parameter: name + whether it carries a type annotation.
///
/// Fact-fed from the adapter's identifier parameter list. The return checker
/// gates on `annotated` only; the call-site checker additionally needs
/// `annotation` (arg-type checks) plus `optional` and `is_rest` (range
/// arity: `min` counts the required prefix, `max` the fixed total, rest is
/// `min`-or-more with the `T[]` element type checking the extras).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionParam {
    /// Parameter name as written.
    pub name: String,
    /// Whether the parameter carries a type annotation.
    pub annotated: bool,
    /// Raw annotation text (`Some("number")`); `None` when unannotated.
    pub annotation: Option<String>,
    /// `true` for `b?: number` and defaulted `b: T = …` (arity is a range).
    pub optional: bool,
    /// `true` for `...rest: T[]` (variadic).
    pub is_rest: bool,
}

/// A straight-line `return <expr>;`: literal kind plus object members.
///
/// Shapes reuse [`InitKind`]/[`ObjectInit`] so the return delegates to the
/// existing check paths unchanged: `kind` is the literal kind (`None` iff
/// the return is an object or array literal), `init_object` the member facts
/// (always fresh — only direct syntactic literals carry them), `init_array`
/// the element facts for `[ ... ]` returns. A
/// `Some(NonLiteral)` kind declines before delegation; the impossible pairs
/// (`Some` + `Some`, `None` + `None`) delegate into the shared
/// contradictory/missing unsupported paths rather than growing
/// function-specific ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionReturn {
    /// Literal kind; `None` iff the return is an object or array literal.
    pub kind: Option<InitKind>,
    /// Object-literal members when the return is `{ ... }`; `None` otherwise.
    pub init_object: Option<ObjectInit>,
    /// Array-literal members when the return is `[ ... ]`; `None` otherwise.
    pub init_array: Option<ArrayInit>,
    /// Outermost assertion facts when the return is an `as` / `satisfies` /
    /// angle assertion (`None` otherwise). Rides the synthetic [`ConstDecl`]
    /// into [`check_one`], so returns share the const cast rule exactly.
    pub cast: Option<CastInput>,
}

/// One leading `const`/`let` declarator inside a straight-line body.
///
/// Driver-mapped from the adapter's [`InnerDeclFact`] (mechanical field
/// copies, exactly like [`FunctionReturn`]): binder identity plus the
/// annotation text and the initializer shape. Object initializers park
/// their shape in `init_object` (always fresh — only direct syntactic
/// literals carry member facts) with `init` reading `None`; every other
/// initializer classifies into `init` directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InnerDecl {
    /// Declarator name, resolved scope-sensitively through the [`Binder`].
    pub name: String,
    /// Fallback span, used only when neither `symbol` nor scope-sensitive
    /// resolution finds the declaration in the [`Binder`].
    pub span: Span,
    /// Per-file scope index of the declarator (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity when the driver resolved it (preferred over
    /// scope-sensitive lookup); must come from the same `file`/`Binder`.
    pub symbol: Option<SymbolId>,
    /// `const` vs `let`; same checking rules (mutability unchecked).
    pub kind: DeclKind,
    /// Raw annotation text; `None` means unannotated.
    pub annotation: Option<String>,
    /// Initializer literal kind; `None` for object/array literals (whose
    /// shapes live in `init_object`/`init_array`) or missing initializers.
    pub init: Option<InitKind>,
    /// Object-literal members when the initializer is `{ ... }`; `None`
    /// otherwise.
    pub init_object: Option<ObjectInit>,
    /// Array-literal members when the initializer is `[ ... ]`; `None`
    /// otherwise.
    pub init_array: Option<ArrayInit>,
    /// Outermost assertion facts when the initializer is an `as` /
    /// `satisfies` / angle assertion (`None` otherwise). Rides the synthetic
    /// [`ConstDecl`] into [`check_one`], so leading positions share the
    /// const cast rule exactly.
    pub cast: Option<CastInput>,
}

/// A straight-line body: leading declarators plus the terminal return.
///
/// Driver-mapped from the adapter's straight [`FunctionBodyFact`] variant
/// (mechanical field copies). Each position delegates through its own
/// synthetic [`ConstDecl`] with its own occurrence node, so per-occurrence
/// join state lives in [`FreshnessTable`] and the [`QueryDb`] memo à la
/// H-002, and counts/messages match tsc's per-position verdicts (probed
/// 7.0.2 P031).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StraightBody {
    /// Leading declarator positions in source order (blocks flattened).
    pub leading: Vec<InnerDecl>,
    /// The terminal `return` position.
    pub tail: FunctionReturn,
}

/// Body shapes of one function declaration.
///
/// [`FunctionBody::SingleReturn`] plus the three P023 joins check through
/// the synthetic-const delegation (each return gets its own synthetic
/// [`ConstDecl`] with its own occurrence node, so per-occurrence join state
/// lives in [`FreshnessTable`] and the [`QueryDb`] memo à la H-002); the
/// P031 [`FunctionBody::StraightBody`] delegates each leading declarator
/// plus the terminal return the same way, as does the P039
/// [`FunctionBody::TryCatch`] per arm (plus the optional tail), the P040
/// [`FunctionBody::Switch`] per case (plus the optional default), the P041
/// [`FunctionBody::CountedFor`] per position (loop body plus the optional
/// tail), the P043 [`FunctionBody::GuardThrow`] tail, and the P043
/// [`FunctionBody::StraightThrow`] leadings (plus the optional tail); the
/// rest decline to [`UnsupportedDecl`] with distinct reasons.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionBody {
    /// Exactly one statement, `return <expr>;` with an argument.
    SingleReturn(FunctionReturn),
    /// Exactly two statements, `return <expr>;` twice: tsc checks both
    /// (unreachable or not — probed 7.0.2, see the module probe record).
    SequenceReturns(JoinedReturns),
    /// Exactly two statements, `if (c) <divergent return>;` with no `else`
    /// plus a trailing `return <expr>;`: tsc checks the guard-branch return
    /// and the tail return independently (probed 7.0.2).
    GuardReturn(JoinedReturns),
    /// Exactly one statement, `if (c) { return A; } else { return B; }`:
    /// tsc checks each branch return independently (probed 7.0.2).
    BranchReturns(JoinedReturns),
    /// Exactly one statement, `try { return A; } catch { return B; }`
    /// (each arm exactly one `return <expr>;`), plus an optional trailing
    /// literal `return C;`: tsc checks each position independently
    /// (probed 7.0.2 P039). Each position delegates through its own
    /// synthetic [`ConstDecl`] with its own occurrence node, exactly like
    /// the P023 joins (no fixpoint, single pass).
    TryCatch(TryCatchBody),
    /// Exactly one statement, `switch (x)` with literal case labels, each
    /// case (plus the optional default) exactly one `return <expr>;`: tsc
    /// checks each position independently (probed 7.0.2 P040). Each position
    /// delegates through its own synthetic [`ConstDecl`] with its own
    /// occurrence node, exactly like the P023 joins (no fixpoint, single
    /// pass).
    Switch(SwitchBody),
    /// Exactly one statement, a counted `for (let i = 0; i < N; i++)` with
    /// literal numeric bounds whose body is exactly one `return <expr>;`,
    /// plus an optional trailing `return`: tsc checks each position
    /// independently (probed 7.0.2 P041). Each position delegates through
    /// its own synthetic [`ConstDecl`] with its own occurrence node,
    /// exactly like the P023 joins (no fixpoint, single pass —
    /// loop-carried verdicts are a pinned gap, see the module rules).
    CountedFor(CountedForBody),
    /// Leading `const`/`let` declarators plus a terminal literal `return`
    /// (single-level blocks flattened): tsc checks each position
    /// independently (probed 7.0.2 P031). Each position delegates through
    /// its own synthetic [`ConstDecl`].
    StraightBody(StraightBody),
    /// Exactly two statements, `if (c) throw ...;` with no `else` plus a
    /// trailing `return <expr>;`: tsc checks the tail return while the throw
    /// accepts any value (probed 7.0.2 P043). The throw emits no verdict and
    /// carries no facts; the tail delegates through its synthetic
    /// [`ConstDecl`] exactly like the P023 guard tail.
    GuardThrow(GuardThrowBody),
    /// A straight-line body holding at least one `throw`: leading
    /// `const`/`let` declarators (blocks flattened) with a terminal literal
    /// `return` or a terminal `throw`. Throws emit no verdict and carry no
    /// facts; each other position delegates through its own synthetic
    /// [`ConstDecl`] exactly like [`FunctionBody::StraightBody`] (a lone
    /// `throw` is the empty, tail-less form and checks silently).
    StraightThrow(StraightThrowBody),
    /// No body node: `declared` tells `declare function` apart from an
    /// overload signature.
    NoBody {
        /// `true` for `declare function` (ambient, never has a body).
        declared: bool,
    },
    /// A body with no statements.
    Empty,
    /// A `try` body outside the checkable [`FunctionBody::TryCatch`]
    /// shape: the frontend recorded why (`finally` clause, destructured
    /// catch pattern, `throw` statement, or a non-straight arm/tail).
    /// Shaping declines with the reason verbatim — never a partial verdict.
    TryUnsupported {
        /// Frontend-recorded decline reason.
        reason: String,
    },
    /// A `switch` body outside the checkable [`FunctionBody::Switch`]
    /// shape: the frontend recorded why (fallthrough, complex case,
    /// case-level declarations, non-literal discriminant or label, or a
    /// duplicate default). Shaping declines with the reason verbatim —
    /// never a partial verdict.
    SwitchUnsupported {
        /// Frontend-recorded decline reason.
        reason: String,
    },
    /// A loop body outside the checkable [`FunctionBody::CountedFor`]
    /// shape: the frontend recorded why (non-literal or non-numeric bound,
    /// non-idiom header, non-`for` loop, infinite `for(;;)`,
    /// `break`/`continue` body, or a complex body/tail). Shaping declines
    /// with the reason verbatim — never a partial verdict.
    LoopUnsupported {
        /// Frontend-recorded decline reason.
        reason: String,
    },
    /// Anything else: longer/multi-path bodies (including a loop or `switch`
    /// statement paired with a non-return statement), `else-if` chains,
    /// `if/else` plus a tail return, `throw`/bare branches outside admitted
    /// throw positions, `continue`, bare or missing `return`.
    Complex,
}

/// Two checkable returns sharing one return annotation (P023 joins).
///
/// Driver-mapped from the adapter's joined [`FunctionBodyFact`] variants
/// (mechanical field copies, each return exactly like [`FunctionReturn`]).
/// Field order is source order; which end is the guard/tail or then/else
/// branch is fixed by the enclosing [`FunctionBody`] variant. Each return
/// delegates through its own synthetic [`ConstDecl`] with its own occurrence
/// node (see [`check_functions`]), so join state stays per-occurrence
/// (H-002) and counts/messages match tsc's per-return verdicts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinedReturns {
    /// The first return in source order (guard return / then-branch return).
    pub first: FunctionReturn,
    /// The second return in source order (tail return / else-branch return).
    pub second: FunctionReturn,
}

/// A checkable `try/catch` body (P039): one return per arm plus an
/// optional trailing return, each checked independently.
///
/// Driver-mapped from the adapter's try/catch fact variant (mechanical
/// field copies, each position exactly like [`FunctionReturn`]). Each
/// position delegates through its own synthetic [`ConstDecl`] with its own
/// occurrence node (see [`check_functions`]), so per-occurrence state
/// stays in [`FreshnessTable`] and the [`QueryDb`] memo à la H-002, and
/// counts/messages match tsc's per-position verdicts (no fixpoint, single
/// pass — the P023 join semantics).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TryCatchBody {
    /// The `try` block's `return` position.
    pub try_branch: FunctionReturn,
    /// The `catch` block's `return` position.
    pub catch_branch: FunctionReturn,
    /// The trailing `return` position, when present.
    pub tail: Option<FunctionReturn>,
}

/// A checkable `switch` body (P040): one return per `case` plus the
/// optional `default` return, each checked independently.
///
/// Driver-mapped from the adapter's switch fact variant (mechanical field
/// copies, each position exactly like [`FunctionReturn`]). Each position
/// delegates through its own synthetic [`ConstDecl`] with its own
/// occurrence node (see [`check_functions`]), so per-occurrence state stays
/// in [`FreshnessTable`] and the [`QueryDb`] memo à la H-002, and
/// counts/messages match tsc's per-position verdicts (no fixpoint, single
/// pass — the P023 join semantics).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwitchBody {
    /// One `return` position per `case` clause, in source order.
    pub cases: Vec<FunctionReturn>,
    /// The `default` clause's `return` position, when present.
    pub default: Option<FunctionReturn>,
}

/// A checkable counted-`for` body (P041): the loop-body return plus the
/// optional trailing return, each checked independently.
///
/// Driver-mapped from the adapter's counted-`for` fact variant (mechanical
/// field copies, each position exactly like [`FunctionReturn`]). Each
/// position delegates through its own synthetic [`ConstDecl`] with its own
/// occurrence node (see [`check_functions`]), so per-occurrence state stays
/// in [`FreshnessTable`] and the [`QueryDb`] memo à la H-002, and
/// counts/messages match tsc's per-position verdicts (no fixpoint, single
/// pass — the P023 join semantics; loop-carried verdicts are a pinned gap,
/// see the module-level counted-`for` rules).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CountedForBody {
    /// The loop body's `return` position.
    pub body: FunctionReturn,
    /// The trailing `return` position, when present.
    pub tail: Option<FunctionReturn>,
}

/// A checkable guard-throw body (P043): the trailing `return` after an
/// `if`-without-`else` guard `throw`, checked through the same synthetic
/// delegation as the P023 guard tail (no fixpoint, single pass).
///
/// Driver-mapped from the adapter's guard-throw fact variant (mechanical
/// field copies, each position exactly like [`FunctionReturn`]). The guard
/// throw carries no facts: `throw` accepts any value in tsc (probed 7.0.2),
/// so the position emits no verdict and needs no span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuardThrowBody {
    /// The trailing `return`'s expression facts.
    pub tail: FunctionReturn,
}

/// A checkable straight-with-throw body (P043): leading declarators plus an
/// optional terminal return, with at least one `throw` skipped
/// classification-side (throws emit no verdict and carry no facts — probed
/// 7.0.2). Each recorded position delegates through its own synthetic
/// [`ConstDecl`] with its own occurrence node, exactly like [`StraightBody`]
/// (no fixpoint, single pass).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StraightThrowBody {
    /// Leading declarator positions in source order (blocks flattened).
    pub leading: Vec<InnerDecl>,
    /// The terminal `return` position, when present (a terminal `throw`
    /// leaves no tail to check).
    pub tail: Option<FunctionReturn>,
}

/// One `function name(params): ret` declaration to check.
///
/// `name`/`span`/`scope`/`symbol` locate the declaration exactly like
/// [`ConstDecl`]; `params`/`params_complex`/`return_annotation`/`body` are
/// fact-fed from the adapter's function declarator facts (only the
/// literal-kind enum mapping is driver-side, mechanical and exhaustive).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionDecl {
    /// Declared name, resolved scope-sensitively through the [`Binder`].
    pub name: String,
    /// Fallback span, used only when neither `symbol` nor scope-sensitive
    /// resolution finds the declaration in the [`Binder`].
    pub span: Span,
    /// Per-file scope index of the declarator (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity when the driver resolved it (preferred over
    /// scope-sensitive lookup); must come from the same `file`/`Binder`.
    pub symbol: Option<SymbolId>,
    /// Identifier parameters in source order (names only; a prefix when
    /// `params_complex`).
    pub params: Vec<FunctionParam>,
    /// `true` when the parameter list holds an unrepresentable pattern:
    /// the declaration declines regardless of `params`.
    pub params_complex: bool,
    /// `true` for `async function` declarations. Hand-fed per fixture until
    /// the adapter emits an async fact (see the module-level P034 BLOCKER):
    /// only async functions unwrap `Promise<T>` returns; non-async
    /// `Promise` returns decline instead of mis-checking.
    pub is_async: bool,
    /// `true` when the declaration carries type parameters (`<T>`, ...).
    /// Driver-mapped from the adapter's type-parameter facts (mirroring
    /// [`ClassDecl::has_type_params`]). Overload resolution declines generic
    /// signatures with a distinct reason instead of resolving them.
    pub has_type_params: bool,
    /// Raw return annotation text; `None` means unannotated.
    pub return_annotation: Option<String>,
    /// Body shape; single returns, the three P023 joins, P031 straight
    /// bodies, P039 try/catch bodies, P040 switch bodies, P041 counted-`for`
    /// bodies, and P043 throw bodies are checkable.
    pub body: FunctionBody,
}

/// Maps a primitive annotation name to its builtin [`TypeId`].
///
/// Returns `None` for anything outside the six-name subset. Union text is
/// detected by callers via `'|'` before reaching this map, so `None` here
/// always means "unknown name" (diagnose), never "out of subset".
#[must_use]
pub fn annotation_type(name: &str) -> Option<TypeId> {
    match name.trim() {
        "number" => Some(TypeStore::NUMBER),
        "string" => Some(TypeStore::STRING),
        "boolean" => Some(TypeStore::BOOLEAN),
        "void" => Some(TypeStore::VOID),
        "undefined" => Some(TypeStore::UNDEFINED),
        "null" => Some(TypeStore::NULL),
        _ => None,
    }
}

/// Maps a boundary annotation name to its builtin [`TypeId`].
///
/// `any`, `unknown`, and `never` live outside [`annotation_type`] on
/// purpose: narrowing, generics, and union-piece classification call that
/// map, and admitting boundary names there would change their decline
/// behavior (probed divergences the subset keeps). Only the annotation/cast
/// policy ([`check_one`], [`classify_param`]) consults this map.
#[must_use]
pub fn boundary_annotation_type(name: &str) -> Option<TypeId> {
    match name.trim() {
        "any" => Some(TypeStore::ANY),
        "unknown" => Some(TypeStore::UNKNOWN),
        "never" => Some(TypeStore::NEVER),
        _ => None,
    }
}

/// Strips all ASCII whitespace so generic wrappers match regardless of
/// source spacing (`Array <number>` reads `Array<number>`).
fn compact_annotation(annotation: &str) -> String {
    annotation.chars().filter(|c| !c.is_whitespace()).collect()
}

/// One admitted array element type: its canonical spelling plus its builtin
/// [`TypeId`]. `any`/`unknown` admit every element silently; `never`
/// diagnoses every literal element with its widened name (probed 7.0.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ArrayElement {
    /// Canonical element spelling for messages (`number`, `any`, ...).
    spelling: &'static str,
    /// Builtin [`TypeId`] members compare against.
    id: TypeId,
}

/// Outcome of [`classify_array_annotation`]: admit with the element type,
/// or decline with the reason.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ArrayAnnotation {
    /// `Array<T>` / `T[]` with a single primitive-or-boundary `T`.
    Admit(ArrayElement),
    /// Array-like but outside the subset (bare `Array`, multi-arg,
    /// union/nested/complex/`void` elements).
    Decline(String),
}

/// Classifies one element type text into its builtin [`TypeId`] plus its
/// canonical message spelling, or `None` for non-primitive shapes.
fn classify_element_type(text: &str) -> Option<ArrayElement> {
    if let Some(id) = annotation_type(text) {
        let spelling = match id {
            id if id == TypeStore::NUMBER => "number",
            id if id == TypeStore::STRING => "string",
            id if id == TypeStore::BOOLEAN => "boolean",
            id if id == TypeStore::NULL => "null",
            id if id == TypeStore::UNDEFINED => "undefined",
            _ => return None,
        };
        return Some(ArrayElement { spelling, id });
    }
    if let Some(id) = boundary_annotation_type(text) {
        let spelling = if id == TypeStore::ANY {
            "any"
        } else if id == TypeStore::UNKNOWN {
            "unknown"
        } else {
            "never"
        };
        return Some(ArrayElement { spelling, id });
    }
    None
}

/// Classifies one annotation as an array spelling (`Array<T>` or `T[]`).
///
/// Returns `None` for non-array spellings (the caller falls through to the
/// union/lib/primitive paths). Single primitive-or-boundary elements admit;
/// everything else array-shaped declines with a distinct reason — never a
/// forced verdict, never a false `TS2304`.
fn classify_array_annotation(annotation: &str) -> Option<ArrayAnnotation> {
    let compact = compact_annotation(annotation);
    if let Some(inner) = compact
        .strip_prefix("Array<")
        .and_then(|rest| rest.strip_suffix('>'))
    {
        return Some(classify_array_element(inner, annotation));
    }
    if compact == "Array" {
        return Some(ArrayAnnotation::Decline(format!(
            "array annotation '{annotation}' needs exactly one type argument: \
            generic arity is outside the subset"
        )));
    }
    if let Some(element) = compact.strip_suffix("[]") {
        if element.is_empty() || element.starts_with('[') {
            return None;
        }
        return Some(classify_array_suffix_element(element, annotation));
    }
    None
}

/// Classifies the `T` in `Array<T>`: arity, then element shape.
fn classify_array_element(inner: &str, annotation: &str) -> ArrayAnnotation {
    if inner.is_empty() || inner.contains(',') {
        return ArrayAnnotation::Decline(format!(
            "array annotation '{annotation}' needs exactly one type argument: \
            generic arity is outside the subset"
        ));
    }
    classify_admitted_element(inner, "array")
}

/// Classifies the `T` in `T[]`, catching the `readonly` prefix the suffix
/// form (but not `Array<T>`) admits in tsc. The prefix test reads the
/// uncompacted annotation so `readonlyx[]` (an unknown element, not a
/// readonly array) keeps its element decline.
fn classify_array_suffix_element(element: &str, annotation: &str) -> ArrayAnnotation {
    if let Some(rest) = element.strip_prefix("readonly") {
        if annotation.contains("readonly ") {
            return ArrayAnnotation::Decline(format!(
                "readonly array element type '{rest}' is outside the subset"
            ));
        }
    }
    classify_admitted_element(element, "array")
}

/// Admits primitive-or-boundary elements; declines union, nested, `void`,
/// and complex shapes with distinct reasons.
fn classify_admitted_element(inner: &str, kind: &str) -> ArrayAnnotation {
    if inner.contains('|') {
        return ArrayAnnotation::Decline(format!(
            "union {kind} element type '{inner}' is outside the subset"
        ));
    }
    if inner.trim() == "void" {
        return ArrayAnnotation::Decline(format!(
            "{kind} element type 'void' is outside the subset"
        ));
    }
    if classify_array_annotation(inner).is_some() || classify_promise_annotation(inner).is_some() {
        return ArrayAnnotation::Decline(format!(
            "nested {kind} element type '{inner}' is outside the subset"
        ));
    }
    match classify_element_type(inner) {
        Some(element) => ArrayAnnotation::Admit(element),
        None => ArrayAnnotation::Decline(format!(
            "{kind} element type '{inner}' is outside the subset"
        )),
    }
}

/// One admitted promise payload: a primitive-or-boundary `T`, or an
/// `Array<U>` whose members then check member-wise.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PromiseInner {
    /// `Promise<T>` with primitive-or-boundary `T` (`any`/`unknown` admit
    /// every return silently).
    Element(ArrayElement),
    /// `Promise<Array<U>>` / `Promise<U[]>` with primitive-or-boundary `U`.
    Array(ArrayElement),
}

impl PromiseInner {
    /// The unwrapped annotation spelling async returns check against:
    /// `T` directly, or the suffix form `U[]` (tsc's canonical expected
    /// spelling — probed 7.0.2).
    fn spelling(self) -> String {
        match self {
            Self::Element(element) => element.spelling.to_owned(),
            Self::Array(element) => format!("{}[]", element.spelling),
        }
    }
}

/// Outcome of [`classify_promise_annotation`]: admit with the payload, or
/// decline with the reason.
#[derive(Clone, Debug, PartialEq, Eq)]
enum PromiseAnnotation {
    /// `Promise<T>` with a checkable `T`.
    Admit(PromiseInner),
    /// Promise-like but outside the subset (bare/multi-arg, union/complex/
    /// `void`/`never` payloads — `never` needs literal value facts for its
    /// literal spelling, probed 7.0.2).
    Decline(String),
}

/// Classifies one annotation as a promise spelling (`Promise<T>`).
///
/// Returns `None` for non-promise spellings (bare `Promise` falls through
/// to the lib gate, which declines it with the arity reason).
fn classify_promise_annotation(annotation: &str) -> Option<PromiseAnnotation> {
    let compact = compact_annotation(annotation);
    let inner = compact
        .strip_prefix("Promise<")
        .and_then(|rest| rest.strip_suffix('>'))?;
    if inner.is_empty() || inner.contains(',') {
        return Some(PromiseAnnotation::Decline(format!(
            "promise annotation '{annotation}' needs exactly one type argument: \
            generic arity is outside the subset"
        )));
    }
    Some(classify_promise_payload(inner))
}

/// Admits primitive, `any`/`unknown`, and single-primitive-array payloads;
/// declines union, `void`, `never`, nested, and complex shapes.
fn classify_promise_payload(inner: &str) -> PromiseAnnotation {
    if inner.contains('|') {
        return PromiseAnnotation::Decline(format!(
            "union promise element type '{inner}' is outside the subset"
        ));
    }
    if inner.trim() == "void" {
        return PromiseAnnotation::Decline(
            "promise element type 'void' is outside the subset".to_owned(),
        );
    }
    if classify_promise_annotation(inner).is_some() {
        return PromiseAnnotation::Decline(format!(
            "nested promise element type '{inner}' is outside the subset"
        ));
    }
    if let Some(array) = classify_array_annotation(inner) {
        return match array {
            ArrayAnnotation::Admit(element) => {
                PromiseAnnotation::Admit(PromiseInner::Array(element))
            }
            ArrayAnnotation::Decline(reason) => PromiseAnnotation::Decline(reason),
        };
    }
    match classify_element_type(inner) {
        Some(element) if element.id == TypeStore::NEVER => PromiseAnnotation::Decline(
            "promise element type 'never' needs literal value facts: outside the subset".to_owned(),
        ),
        Some(element) => PromiseAnnotation::Admit(PromiseInner::Element(element)),
        None => PromiseAnnotation::Decline(format!(
            "promise element type '{inner}' is outside the subset"
        )),
    }
}

/// Lib heads by family: utility/mapped types, collections, iterables,
/// binary buffers plus typed arrays, and DOM types.
const UTILITY_HEADS: &[&str] = &[
    "Record",
    "Partial",
    "Required",
    "Readonly",
    "Pick",
    "Omit",
    "Exclude",
    "Extract",
    "NonNullable",
    "Awaited",
    "ReturnType",
    "Parameters",
    "ConstructorParameters",
    "InstanceType",
    "ThisType",
    "Uppercase",
    "Lowercase",
    "Capitalize",
    "Uncapitalize",
];
/// Collection constructors with generic arity.
const COLLECTION_HEADS: &[&str] = &["Map", "Set", "WeakMap", "WeakSet"];
/// Iteration protocol types.
const ITERABLE_HEADS: &[&str] = &[
    "Iterable",
    "Iterator",
    "IterableIterator",
    "AsyncIterable",
    "AsyncIterator",
    "Generator",
];
/// Binary buffers plus typed arrays.
const TYPED_ARRAY_HEADS: &[&str] = &[
    "ArrayBuffer",
    "SharedArrayBuffer",
    "DataView",
    "Int8Array",
    "Uint8Array",
    "Uint8ClampedArray",
    "Int16Array",
    "Uint16Array",
    "Int32Array",
    "Uint32Array",
    "Float32Array",
    "Float64Array",
    "BigInt64Array",
    "BigUint64Array",
];
/// Ambient DOM types with no value-semantics facts in the subset.
const DOM_HEADS: &[&str] = &[
    "Console",
    "Window",
    "Document",
    "Element",
    "HTMLElement",
    "Node",
    "Event",
    "EventTarget",
    "Navigator",
    "Location",
    "History",
    "Storage",
    "Request",
    "Response",
    "Headers",
    "FormData",
    "URL",
    "URLSearchParams",
    "XMLHttpRequest",
];

/// Whether `head` names a lib type of one family: utility/mapped types,
/// collections, iterables, binary buffers plus typed arrays, or DOM types.
/// Structural admission only (no `.d.ts` modeling anywhere): every match
/// declines with a family reason, never a false `TS2304`.
fn lib_family(head: &str) -> Option<&'static str> {
    if UTILITY_HEADS.contains(&head) {
        Some("utility")
    } else if COLLECTION_HEADS.contains(&head) {
        Some("collection")
    } else if ITERABLE_HEADS.contains(&head) {
        Some("iterable")
    } else if TYPED_ARRAY_HEADS.contains(&head) {
        Some("typed-array")
    } else if DOM_HEADS.contains(&head) {
        Some("DOM")
    } else {
        None
    }
}

/// The decline reason for a non-admitted lib annotation, or `None` when the
/// annotation is not lib-shaped (the caller falls through to `TS2304`).
///
/// Tuples decline here too: `[number, string]` is lib-adjacent syntax but
/// tuples are NOT arrays, so they need their own reason rather than the
/// array path or a false `TS2304`.
fn lib_decline_reason(annotation: &str) -> Option<String> {
    if annotation.starts_with('[') {
        return Some(format!(
            "tuple annotation '{annotation}' is outside the subset: tuples are not arrays"
        ));
    }
    if annotation.starts_with("readonly ") || annotation.starts_with("readonly\t") {
        return Some(format!(
            "readonly array annotation '{annotation}' is outside the subset"
        ));
    }
    let head = annotation.split('<').next().unwrap_or(annotation).trim();
    if head == "Array" || head == "Promise" {
        return Some(format!(
            "generic annotation '{head}' needs exactly one type argument: \
            generic arity is outside the subset"
        ));
    }
    if head == "ReadonlyArray" {
        return Some(format!(
            "readonly array annotation '{annotation}' is outside the subset"
        ));
    }
    lib_family(head).map(|family| {
        format!("{family} type annotation '{annotation}' is outside the subset: lib modeling")
    })
}

/// Which assertion form one [`CastInput`] records.
///
/// `as` and angle assertions share the oracle rule (`TS2352` on decline);
/// `satisfies` declines differ (`TS1360`) and admit transparently to the
/// operand type instead of the target (both probed on tsc 7.0.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastKind {
    /// `expr as T`.
    As,
    /// `expr satisfies T`.
    Satisfies,
    /// `<T>expr`.
    Angle,
}

/// One `as` / `satisfies` / angle assertion on a checkable position.
///
/// Driver-mapped from the adapter's `CastFact` (mechanical field copies,
/// plus the operand-kind enum translation). `target` is the verbatim target
/// text (`""` when the fact was unsliceable — always complex, never
/// mis-checked).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CastInput {
    /// Literal kind of the operand (`NonLiteral`/`Unknown` always decline).
    pub operand: InitKind,
    /// Raw target text (`Some("number")`); driver echoes `""` for
    /// unsliceable facts so they decline instead of going missing.
    pub target: String,
    /// Span of the operand expression (the oracle's `TS2352` anchor).
    pub operand_span: Span,
    /// Which assertion form.
    pub kind: CastKind,
}

/// An admitted or declined cast's result type: what flows downstream.
///
/// `as`/angle results follow the target; `satisfies` results stay the
/// operand type (probed tsc 7.0.2). `Any` and `Never` results accept every
/// annotation (`never` is assignable to all, `any` both ways), so both
/// silence the position; `Unknown` checks like a literal spelling
/// `unknown` (diagnosing against `T`, clean against `any`/`unknown`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CastType {
    /// Target (or operand) `any`: downstream always clean.
    Any,
    /// Target `unknown`: downstream diagnoses `TS2322` against `T`.
    Unknown,
    /// Target `never`: downstream always clean.
    Never,
    /// A primitive kind (target for `as`/angle, operand for `satisfies`).
    Literal(InitKind),
}

impl CastType {
    /// The downstream [`InitKind`], or `None` for accept-all results.
    fn into_init(self) -> Option<InitKind> {
        match self {
            Self::Any | Self::Never => None,
            Self::Unknown => Some(InitKind::Unknown),
            Self::Literal(kind) => Some(kind),
        }
    }
}

/// Outcome of [`evaluate_cast`]: admit or decline with the downstream
/// [`CastType`], or complex with the decline reason.
#[derive(Clone, Debug, PartialEq, Eq)]
enum CastEvaluation {
    /// The assertion holds: check the result through the existing path.
    Admit(CastType),
    /// The assertion fails: diagnose, then still check the result
    /// (probed: declined casts never suppress the downstream check).
    Decline(CastType),
    /// Unevaluatable (non-literal operand, unparseable target): decline
    /// the whole position with the reason, never a forced verdict.
    Complex(String),
}

/// Classifies one cast target text: boundary names plus the six primitives
/// (`void` rides `undefined`: `1 as void` declines exactly like
/// `1 as undefined`, probed shape). Anything else (unions, objects,
/// aliases, literal types, `const`, empty) is `None` — outside the subset.
fn classify_cast_target(text: &str) -> Option<CastType> {
    match text.trim() {
        "any" => Some(CastType::Any),
        "unknown" => Some(CastType::Unknown),
        "never" => Some(CastType::Never),
        "number" => Some(CastType::Literal(InitKind::Number)),
        "string" => Some(CastType::Literal(InitKind::String)),
        "boolean" => Some(CastType::Literal(InitKind::Boolean)),
        "null" => Some(CastType::Literal(InitKind::Null)),
        "undefined" | "void" => Some(CastType::Literal(InitKind::Undefined)),
        _ => None,
    }
}

/// Applies the probed overlap rule to one assertion.
///
/// Admit iff the operand and target sufficiently overlap: same widened
/// primitive, or a boundary (`any`/`unknown`/`never`) target (probed tsc
/// 7.0.2 — `null as undefined` and `string as number` decline;
/// `true as boolean`, `1 as any`, `"x" as unknown`, and `"x" as never`
/// admit). `uv as string` admits in tsc but stays complex here: identifier
/// operands carry no value-type facts, so the boundary-operand side never
/// evaluates in-subset.
fn evaluate_cast(cast: &CastInput) -> CastEvaluation {
    if matches!(cast.operand, InitKind::NonLiteral | InitKind::Unknown) {
        return CastEvaluation::Complex(
            "cast operand is not a classifiable literal: expression facts are outside the subset"
                .to_owned(),
        );
    }
    let Some(target) = classify_cast_target(cast.target.as_str()) else {
        return CastEvaluation::Complex(format!(
            "cast target '{}' is outside the subset",
            cast.target.trim()
        ));
    };
    let result = match cast.kind {
        CastKind::As | CastKind::Angle => target,
        CastKind::Satisfies => CastType::Literal(cast.operand),
    };
    let overlaps = match target {
        CastType::Any | CastType::Unknown | CastType::Never => true,
        CastType::Literal(wanted) => wanted == cast.operand,
    };
    if overlaps {
        CastEvaluation::Admit(result)
    } else {
        CastEvaluation::Decline(result)
    }
}

/// Emits one cast diagnostic at the operand span (the oracle anchor).
///
/// `as`/angle declines spell `TS2352` with the widened operand name plus
/// the verbatim target text (primitives spell canonically, so verbatim is
/// exact); `satisfies` declines spell `TS1360`.
fn emit_cast_diagnostic(file: FileId, cast: &CastInput, report: &mut FileReport) {
    let target = cast.target.trim();
    match cast.kind {
        CastKind::As | CastKind::Angle => report.diagnostics.push(PithDiagnostic {
            code: CODE_CAST.to_owned(),
            file,
            span: cast.operand_span,
            message: format!(
                "Conversion of type '{}' to type '{target}' may be a mistake \
                because neither type sufficiently overlaps with the other. If \
                this was intentional, convert the expression to 'unknown' first.",
                cast.operand.name()
            ),
        }),
        CastKind::Satisfies => report.diagnostics.push(PithDiagnostic {
            code: CODE_SATISFIES.to_owned(),
            file,
            span: cast.operand_span,
            message: format!(
                "Type '{}' does not satisfy the expected type '{target}'.",
                cast.operand.name()
            ),
        }),
    }
}

/// Per-occurrence freshness side table (E001 refined mode / H-002).
///
/// Maps each object-literal declaration occurrence to whether its literal is
/// fresh (a direct syntactic literal: excess-property checks fire) or stale
/// (aliased through a variable: they must not). Shared structure (member
/// names, builtin [`TypeId`]s) is canonical and global; THIS table holds the
/// occurrence-varying verdict state, keyed by `(file, node)` — never in
/// [`TypeData`]. Stale literals are inexpressible in-subset today (a
/// variable init is [`InitKind::NonLiteral`] and declines earlier), so live
/// entries are all fresh; the table still gates every excess verdict
/// per-occurrence by design, and `false` entries pin the gate in tests.
#[derive(Clone, Debug, Default)]
struct FreshnessTable {
    fresh: HashMap<(FileId, NodeId), bool>,
}

impl FreshnessTable {
    /// Whether the object literal at this occurrence is fresh.
    ///
    /// Missing entries (non-object declarations) report stale: only a
    /// positively recorded fresh literal may diagnose excess members.
    fn is_fresh(&self, file: FileId, node: NodeId) -> bool {
        self.fresh.get(&(file, node)).copied().unwrap_or(false)
    }
}

/// Checks every declarator in `decls` for `file`, threading each annotated
/// declaration's type through `db` (one memoized [`QueryKind::TypeOf`] query
/// per annotated declaration) and returning the sorted [`FileReport`].
///
/// Declaration spans prefer the exact [`SymbolId`] when the driver resolved
/// one, else scope-sensitive [`Binder::resolve`] from the declarator scope;
/// the caller span in [`ConstDecl`] is a fallback only.
#[must_use]
pub fn check_file(
    file: FileId,
    decls: &[ConstDecl],
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    check_file_with_aliases(file, decls, binder, db, &[])
}

/// Checks every `const`/`let` declarator in `decls` for `file` with local
/// type aliases in scope, returning the sorted [`FileReport`].
///
/// `aliases` feeds single-level expansion (P038):
/// alias-to-primitive/boundary annotations check as if the target were
/// written, everything else named declines with a distinct reason.
/// [`check_file`] threads an empty table; [`multifile`] keeps its own
/// import-alias rules and never calls this entry.
#[must_use]
pub fn check_file_with_aliases(
    file: FileId,
    decls: &[ConstDecl],
    binder: &Binder,
    db: &mut QueryDb,
    aliases: &[TypeAliasShape],
) -> FileReport {
    let mut freshness = FreshnessTable::default();
    for (index, decl) in decls.iter().enumerate() {
        if let Some(init) = decl.init_object.as_ref() {
            freshness
                .fresh
                .insert((file, occurrence_node(index)), init.fresh);
        }
    }
    let const_names: Vec<&str> = decls.iter().map(|decl| decl.name.as_str()).collect();
    let scope = LocalAliasScope {
        aliases,
        const_names: &const_names,
    };
    let mut report = FileReport::default();
    for (index, decl) in decls.iter().enumerate() {
        let mut ctx = CheckCtx {
            file,
            node: occurrence_node(index),
            db: &mut *db,
            freshness: &freshness,
            report: &mut report,
            extra: &[],
        };
        check_one(decl, binder, &mut ctx, &scope);
    }
    sort_report(&mut report);
    report
}

/// Sorts a [`FileReport`] by `(file, span.lo, span.hi)` on both sinks so
/// repeated runs agree byte-for-byte.
fn sort_report(report: &mut FileReport) {
    report.diagnostics.sort_by(|left, right| {
        (left.file, left.span.lo, left.span.hi).cmp(&(right.file, right.span.lo, right.span.hi))
    });
    report.unsupported.sort_by(|left, right| {
        (left.file, left.span.lo, left.span.hi).cmp(&(right.file, right.span.lo, right.span.hi))
    });
}

/// Checks every function declaration in `decls` for `file`, returning the
/// sorted [`FileReport`].
///
/// Gates (at most one note per declaration, structural first):
/// unrepresentable parameter patterns, unannotated parameters, missing
/// return annotation, then non-straight-line bodies all decline to
/// [`UnsupportedDecl`]. Checkable declarations (identifier params all
/// annotated, return annotated, single literal `return`, one of the three
/// P023 joins, a P031 straight body, a P039 try/catch, a P040 switch, a
/// P041 counted-`for`, or a P043 guard-throw or straight-with-throw)
/// delegate to the same [`check_one`]
/// path as [`check_file`]
/// through synthetic [`ConstDecl`]s — one per return position, each with its
/// own occurrence node, the return literal as initializer, always fresh — so
/// verdicts and messages match the const/object subset by construction, and
/// per-return counts match tsc's per-return verdicts (probed 7.0.2).
///
/// Occurrence identity lives in a disjoint node range (see
/// `function_occurrence_node`): consts and functions for one file may share
/// a [`QueryDb`] without aliasing memo entries.
///
/// Driver contract (no double-report): an inner `const` inside a straight
/// body emits BOTH a `DeclFact` and an inner body position. Never feed one
/// file to both [`check_file`] and [`check_functions`] (or merge their
/// reports) without deduplicating inner consts — every current driver
/// checks exactly one family per file.
#[must_use]
pub fn check_functions(
    file: FileId,
    decls: &[FunctionDecl],
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    let mut synth: Vec<ConstDecl> = Vec::with_capacity(decls.len());
    let mut report = FileReport::default();
    for decl in decls {
        let span = binder_span_for(binder, file, &decl.name, decl.scope, decl.symbol, decl.span);
        match function_shape(decl) {
            Ok(shaped) => {
                for shaped_return in shaped.returns {
                    synth.push(ConstDecl {
                        name: shaped_return.site.name,
                        span: shaped_return.site.span,
                        scope: shaped_return.site.scope,
                        symbol: shaped_return.site.symbol,
                        kind: shaped_return.site.kind,
                        annotation: shaped_return.site.annotation,
                        init: shaped_return.kind,
                        init_object: shaped_return.init_object,
                        init_array: shaped_return.init_array,
                        cast: shaped_return.cast,
                    });
                }
            }
            Err(reason) => report
                .unsupported
                .push(UnsupportedDecl { file, span, reason }),
        }
    }
    let mut freshness = FreshnessTable::default();
    for (index, decl) in synth.iter().enumerate() {
        if let Some(init) = decl.init_object.as_ref() {
            freshness
                .fresh
                .insert((file, function_occurrence_node(index)), init.fresh);
        }
    }
    for (index, decl) in synth.iter().enumerate() {
        let mut ctx = CheckCtx {
            file,
            node: function_occurrence_node(index),
            db: &mut *db,
            freshness: &freshness,
            report: &mut report,
            extra: &[],
        };
        // Function returns thread no alias tables (pinned P038 gap: return
        // annotations naming aliases keep today's verdicts).
        check_one(decl, binder, &mut ctx, &LocalAliasScope::EMPTY);
    }
    sort_report(&mut report);
    report
}

/// Identity plus annotation for one synthetic checkable position:
/// everything [`check_one`] needs beyond the literal shape. Return
/// positions reuse the declaration's identity with the return annotation;
/// straight-body leading positions carry the declarator's own identity
/// with its own annotation, so per-position diagnostics anchor at their
/// own spans (probed 7.0.2 P031).
#[derive(Clone, Debug)]
struct SynthSite {
    /// Declared name, resolved scope-sensitively through the [`Binder`].
    name: String,
    /// Fallback span, used only when neither `symbol` nor scope-sensitive
    /// resolution finds the declaration in the [`Binder`].
    span: Span,
    /// Per-file scope index of the declarator (from the adapter's facts).
    scope: u32,
    /// Exact binder identity when the driver resolved it (preferred over
    /// scope-sensitive lookup).
    symbol: Option<SymbolId>,
    /// `const` vs `let` vs synthetic function return; same checking rules.
    kind: DeclKind,
    /// Raw annotation text driving the position's check; `None` means
    /// unannotated (only leading positions: returns always annotate).
    annotation: Option<String>,
}

/// One checkable position: the literal kind plus object members for its
/// synthetic [`ConstDecl`] (one per checkable join position, in source
/// order).
#[derive(Clone, Debug)]
struct SynthReturn {
    /// Who and what this position checks.
    site: SynthSite,
    /// Literal kind; `None` iff the position is an object or array literal.
    kind: Option<InitKind>,
    /// Object-literal members when the position is `{ ... }`; `None`
    /// otherwise.
    init_object: Option<ObjectInit>,
    /// Array-literal members when the position is `[ ... ]`; `None`
    /// otherwise.
    init_array: Option<ArrayInit>,
    /// Assertion facts riding into the synthetic [`ConstDecl`].
    cast: Option<CastInput>,
}

/// A checkable function shape: one [`SynthReturn`] per checkable position
/// (one for straight-line single returns, two for P023 joins, leading
/// declarators plus the tail return for P031 straight bodies, arms plus the
/// tail for P039 try/catch, cases plus the default for P040 switch, the
/// loop body plus the tail for P041 counted-`for` — all in
/// source order).
#[derive(Debug)]
struct ShapedBody {
    /// One synthetic position per checkable declaration slot, in source
    /// order.
    returns: Vec<SynthReturn>,
}

/// The declaration-level identity for return positions: the function's own
/// name, span, scope, and symbol with the synthetic [`DeclKind::Function`].
fn return_site(decl: &FunctionDecl, annotation: &str) -> SynthSite {
    SynthSite {
        name: decl.name.clone(),
        span: decl.span,
        scope: decl.scope,
        symbol: decl.symbol,
        kind: DeclKind::Function,
        annotation: Some(annotation.to_owned()),
    }
}

/// Unwraps one `Promise<T>` return annotation for an async function into
/// the `T` its returns check against (`U[]` for `Promise<Array<U>>`, which
/// then checks member-wise); every other annotation passes through
/// unchanged.
///
/// Non-async `Promise` returns decline (tsc spells `TS2322`/`TS2739` shapes
/// the subset cannot spell — never forced), as do uncheckable payloads
/// (each carries its own reason from the promise classifier).
fn promise_effective_annotation(decl: &FunctionDecl, annotation: &str) -> Result<String, String> {
    let Some(promise) = classify_promise_annotation(annotation.trim()) else {
        return Ok(annotation.to_owned());
    };
    match promise {
        PromiseAnnotation::Decline(reason) => Err(reason),
        PromiseAnnotation::Admit(inner) => {
            if !decl.is_async {
                return Err(format!(
                    "non-async function '{}' returns '{annotation}': \
                    promise returns need an async function",
                    decl.name
                ));
            }
            Ok(inner.spelling())
        }
    }
}

/// Shapes one `try/catch` body for [`function_shape`]: the try return, the
/// catch return, then the optional tail return — one [`SynthReturn`] per
/// position in source order, like the P023 join arms (no fixpoint, single
/// pass; see the module-level try/catch rules).
fn shape_try_catch(
    decl: &FunctionDecl,
    body: &TryCatchBody,
    effective: &str,
) -> Result<Vec<SynthReturn>, String> {
    let mut positions = Vec::with_capacity(3);
    positions.push(shape_return(
        &body.try_branch,
        "try return",
        return_site(decl, effective),
    )?);
    positions.push(shape_return(
        &body.catch_branch,
        "catch return",
        return_site(decl, effective),
    )?);
    if let Some(tail) = body.tail.as_ref() {
        positions.push(shape_return(
            tail,
            "tail return",
            return_site(decl, effective),
        )?);
    }
    Ok(positions)
}

/// Shapes one `switch` body for [`function_shape`]: one [`SynthReturn`] per
/// `case` in source order, then the optional `default` — like the P023
/// join arms (no fixpoint, single pass; see the module-level switch rules).
fn shape_switch(
    decl: &FunctionDecl,
    body: &SwitchBody,
    effective: &str,
) -> Result<Vec<SynthReturn>, String> {
    let mut positions = Vec::with_capacity(body.cases.len().saturating_add(1));
    for case in &body.cases {
        positions.push(shape_return(
            case,
            "case return",
            return_site(decl, effective),
        )?);
    }
    if let Some(default) = body.default.as_ref() {
        positions.push(shape_return(
            default,
            "default return",
            return_site(decl, effective),
        )?);
    }
    Ok(positions)
}

/// Shapes one counted-`for` body for [`function_shape`]: the loop-body
/// return, then the optional tail return — one [`SynthReturn`] per position
/// in source order, like the P023 join arms (no fixpoint, single pass; see
/// the module-level counted-`for` rules).
fn shape_counted_for(
    decl: &FunctionDecl,
    body: &CountedForBody,
    effective: &str,
) -> Result<Vec<SynthReturn>, String> {
    let mut positions = Vec::with_capacity(2);
    positions.push(shape_return(
        &body.body,
        "loop return",
        return_site(decl, effective),
    )?);
    if let Some(tail) = body.tail.as_ref() {
        positions.push(shape_return(
            tail,
            "tail return",
            return_site(decl, effective),
        )?);
    }
    Ok(positions)
}

/// Shapes one guard-throw body for [`function_shape`]: the tail return —
/// one [`SynthReturn`] through the same synthetic delegation as the P023
/// guard tail (the guard throw emits no verdict and carries no facts — see
/// the module-level throw rules).
fn shape_guard_throw(
    decl: &FunctionDecl,
    body: &GuardThrowBody,
    effective: &str,
) -> Result<Vec<SynthReturn>, String> {
    Ok(vec![shape_return(
        &body.tail,
        "tail return",
        return_site(decl, effective),
    )?])
}

/// Shapes one straight-with-throw body for [`function_shape`]: leading
/// declarators (unannotated cast-less ones skipped, exactly like
/// [`FunctionBody::StraightBody`]) plus the terminal return when present —
/// one [`SynthReturn`] per recorded position in source order (throws emit
/// no verdict and carry no facts — see the module-level throw rules).
fn shape_straight_throw(
    decl: &FunctionDecl,
    body: &StraightThrowBody,
    effective: &str,
) -> Result<Vec<SynthReturn>, String> {
    let mut positions = Vec::with_capacity(body.leading.len().saturating_add(1));
    for inner in &body.leading {
        if let Some(position) = shape_leading(inner) {
            positions.push(position);
        }
    }
    if let Some(tail) = body.tail.as_ref() {
        positions.push(shape_return(
            tail,
            "tail return",
            return_site(decl, effective),
        )?);
    }
    Ok(positions)
}

/// Gates one function declaration: `Ok` carries the [`ShapedBody`] (one
/// [`SynthReturn`] per checkable position, in source order);
/// `Err` carries the unsupported reason.
fn function_shape(decl: &FunctionDecl) -> Result<ShapedBody, String> {
    if decl.params_complex {
        return Err("non-identifier parameter pattern is outside the subset".to_owned());
    }
    if let Some(param) = decl.params.iter().find(|param| !param.annotated) {
        return Err(format!(
            "unannotated parameter '{}' is outside the subset",
            param.name
        ));
    }
    let Some(annotation) = decl.return_annotation.as_deref() else {
        return Err(format!(
            "no return annotation on '{}': inference is outside the subset",
            decl.name
        ));
    };
    let effective = promise_effective_annotation(decl, annotation)?;
    let returns = match &decl.body {
        FunctionBody::SingleReturn(body) => {
            vec![shape_return(body, "return", return_site(decl, &effective))?]
        }
        FunctionBody::SequenceReturns(join) => vec![
            shape_return(&join.first, "first return", return_site(decl, &effective))?,
            shape_return(&join.second, "second return", return_site(decl, &effective))?,
        ],
        FunctionBody::GuardReturn(join) => vec![
            shape_return(&join.first, "guard return", return_site(decl, &effective))?,
            shape_return(&join.second, "tail return", return_site(decl, &effective))?,
        ],
        FunctionBody::BranchReturns(join) => vec![
            shape_return(
                &join.first,
                "then-branch return",
                return_site(decl, &effective),
            )?,
            shape_return(
                &join.second,
                "else-branch return",
                return_site(decl, &effective),
            )?,
        ],
        FunctionBody::TryCatch(body) => shape_try_catch(decl, body, &effective)?,
        FunctionBody::Switch(body) => shape_switch(decl, body, &effective)?,
        FunctionBody::CountedFor(body) => shape_counted_for(decl, body, &effective)?,
        FunctionBody::GuardThrow(body) => shape_guard_throw(decl, body, &effective)?,
        FunctionBody::StraightThrow(body) => shape_straight_throw(decl, body, &effective)?,
        FunctionBody::StraightBody(straight) => {
            let mut positions = Vec::with_capacity(straight.leading.len().saturating_add(1));
            for inner in &straight.leading {
                if let Some(position) = shape_leading(inner) {
                    positions.push(position);
                }
            }
            positions.push(shape_return(
                &straight.tail,
                "tail return",
                return_site(decl, &effective),
            )?);
            positions
        }
        FunctionBody::NoBody { declared: true } => {
            return Err(format!(
                "declare function '{}' has no body to check",
                decl.name
            ));
        }
        FunctionBody::NoBody { declared: false } => {
            return Err(format!(
                "overload signature for '{}' has no body to check",
                decl.name
            ));
        }
        FunctionBody::Empty => {
            return Err(format!(
                "empty body on '{}': nothing to check against",
                decl.name
            ));
        }
        FunctionBody::TryUnsupported { reason }
        | FunctionBody::SwitchUnsupported { reason }
        | FunctionBody::LoopUnsupported { reason } => {
            return Err(reason.clone());
        }
        FunctionBody::Complex => {
            return Err(format!(
                "complex body on '{}': control flow is outside the subset",
                decl.name
            ));
        }
    };
    Ok(ShapedBody { returns })
}

/// Gates one straight-body leading declarator for the synthetic
/// [`ConstDecl`]: unannotated cast-less declarators are skipped (tsc
/// infers them — no verdict exists at that position, probed 7.0.2 P031),
/// while every other shape delegates (non-literal initializers decline
/// per-position inside `check_one`, never a partial verdict over the
/// remaining positions). The impossible kind/member pairs (`Some` +
/// `Some`, `None` + `None`) pass through into the shared
/// contradictory/missing unsupported paths in [`check_one`].
fn shape_leading(inner: &InnerDecl) -> Option<SynthReturn> {
    if inner.annotation.is_none() && inner.cast.is_none() {
        return None;
    }
    Some(SynthReturn {
        site: SynthSite {
            name: inner.name.clone(),
            span: inner.span,
            scope: inner.scope,
            symbol: inner.symbol,
            kind: inner.kind,
            annotation: inner.annotation.clone(),
        },
        kind: inner.init,
        init_object: inner.init_object.clone(),
        init_array: inner.init_array.clone(),
        cast: inner.cast.clone(),
    })
}

/// Gates one return position for the synthetic [`ConstDecl`]: non-literal
/// returns decline the whole declaration with a position-naming reason
/// (never a partial verdict over the remaining positions). Assertion
/// returns ride through instead: their facts evaluate solver-side in
/// [`check_one`], so the gate must not swallow them. Object and array
/// returns carry their shapes alongside (a bare `NonLiteral` kind with a
/// shape rides into the shared contradictory path in [`check_one`]). The
/// impossible kind/member pairs (`Some` + `Some`, `None` + `None`) pass
/// through into the shared contradictory/missing unsupported paths in
/// [`check_one`].
fn shape_return(
    body: &FunctionReturn,
    position: &str,
    site: SynthSite,
) -> Result<SynthReturn, String> {
    if body.cast.is_some() {
        return Ok(SynthReturn {
            site,
            kind: body.kind,
            init_object: body.init_object.clone(),
            init_array: body.init_array.clone(),
            cast: body.cast.clone(),
        });
    }
    if body.kind == Some(InitKind::NonLiteral)
        && body.init_object.is_none()
        && body.init_array.is_none()
    {
        return Err(format!(
            "non-literal {position} in '{}' is outside the subset",
            site.name
        ));
    }
    Ok(SynthReturn {
        site,
        kind: body.kind,
        init_object: body.init_object.clone(),
        init_array: body.init_array.clone(),
        cast: None,
    })
}

/// One call-site argument: literal kind plus span.
///
/// Fact-fed from the adapter's `CallArgFact`; only the enum mapping is
/// driver-side (mechanical and exhaustive). Kinds reuse [`InitKind`] so
/// argument checks run through [`annotation_type`] and [`InitKind::type_id`]
/// unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallArg {
    /// Literal kind of the argument expression.
    pub kind: InitKind,
    /// Span of the argument expression.
    pub span: Span,
    /// Outermost assertion facts when the argument is an `as` / `satisfies` /
    /// angle assertion (`None` otherwise). Declined casts diagnose at the
    /// operand span; admitted results check like their kind.
    pub cast: Option<CastInput>,
}

/// One direct `f(...)` call site to check.
///
/// Fact-fed from the adapter's `CallFact`: callee name plus its identifier
/// span, the whole call span, and one [`CallArg`] per argument in source
/// order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallSite {
    /// Callee name as written.
    pub callee: String,
    /// Span of the callee identifier (too-few-arity anchor, mirroring tsc).
    pub callee_span: Span,
    /// Span of the whole call expression.
    pub span: Span,
    /// Argument facts in source order.
    pub args: Vec<CallArg>,
}

/// Checks every direct call site in `calls` against the function
/// declarations in `decls` for `file`, returning the sorted [`FileReport`].
///
/// Resolution is by callee name within the file's declaration set (the
/// single-file closed world: every declared name is in `decls`). Per-call
/// outcomes, in order:
///
/// - No declaration bears the name: the call is skipped, never diagnosed.
///   A genuinely undeclared callee is already tracked as an unresolved
///   reference (see [`Binder::unresolved`]) — diagnosing would double-report
///   one signal. A name that is neither declared nor unresolved-tracked is
///   driver skew, recorded as [`UnsupportedDecl`] rather than silently
///   dropped.
/// - Several declarations bear the name: more than one body means shadowing
///   (one [`UnsupportedDecl`] — implementations cannot be disambiguated),
///   else every `NoBody` signature resolves by any-match (see
///   [`check_overload_call`]): generic and otherwise-uncheckable signatures
///   are excluded with distinct reasons (clean when a remaining signature
///   admits the call, one [`UnsupportedDecl`] otherwise), and checkable
///   groups diagnose only when every signature fails (`PITH2769`,
///   `PITH2575`, or the union `PITH2554`/`PITH2555`).
/// - Exactly one declaration: parameter gates (structural first —
///   `params_complex`, non-trailing rest, unannotated, required-after-optional,
///   uncheckable parameter types — each its own [`UnsupportedDecl`] at the
///   callee span), then at most one diagnostic: arity (`PITH2554`, or
///   `PITH2555` below a rest minimum) beats arg types (`PITH2345`),
///   and only the first mismatched argument reports (all probed on tsc
///   7.0.2). Non-literal arguments are skipped per-argument for type checks
///   while arity still enforces. Return annotations and body shapes are
///   irrelevant here: calls to complex-bodied functions still check.
///
/// Spans mirror the oracle: too-few arity at the callee identifier, too-many
/// at the first excess argument, arg-type at the mismatched argument.
#[must_use]
pub fn check_calls(
    file: FileId,
    decls: &[FunctionDecl],
    calls: &[CallSite],
    binder: &Binder,
) -> FileReport {
    let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
    for (index, decl) in decls.iter().enumerate() {
        by_name.entry(decl.name.as_str()).or_default().push(index);
    }
    let mut report = FileReport::default();
    for call in calls {
        check_one_call(file, decls, &by_name, call, binder, &mut report);
    }
    sort_report(&mut report);
    report
}

/// Checks one call site, pushing into `report`.
///
/// At most one diagnostic ever fires per call (arity before types, first
/// mismatch only); declines push exactly one [`UnsupportedDecl`].
fn check_one_call(
    file: FileId,
    decls: &[FunctionDecl],
    by_name: &HashMap<&str, Vec<usize>>,
    call: &CallSite,
    binder: &Binder,
    report: &mut FileReport,
) {
    let candidates = by_name.get(call.callee.as_str());
    let Some(candidates) = candidates else {
        if binder
            .unresolved()
            .iter()
            .any(|entry| entry.file == file && entry.name == call.callee)
        {
            // Tracked as an unresolved reference already: skip, never
            // double-diagnose.
            return;
        }
        report.unsupported.push(UnsupportedDecl {
            file,
            span: call.callee_span,
            reason: format!(
                "call to undeclared name '{}': nothing to check against",
                call.callee
            ),
        });
        return;
    };
    if candidates.len() != 1 {
        let mut run = OverloadRun {
            file,
            decls,
            call,
            report,
        };
        check_overload_call(&mut run, candidates);
        return;
    }
    check_single_call(file, &decls[candidates[0]], call, report);
}

/// Checks one call site against exactly one declaration, pushing into
/// `report`.
///
/// Parameter gates first (each its own [`UnsupportedDecl`] at the callee
/// span), then at most one diagnostic: arity (`PITH2554`, or `PITH2555`
/// below a rest minimum) beats arg types (`PITH2345`), and only the first
/// mismatched argument reports (all probed on tsc 7.0.2).
fn check_single_call(file: FileId, decl: &FunctionDecl, call: &CallSite, report: &mut FileReport) {
    let Some(resolved) = call_params(call, decl, file, report) else {
        return;
    };
    let target = owned_target(resolved);
    let site = VerdictSite {
        anchor: call.callee_span,
        args: &call.args,
    };
    let view = CallTarget {
        fixed: &target.fixed,
        arity: CallArity {
            min: target.min,
            max: target.max,
        },
        rest: target.rest.as_ref(),
    };
    emit_call_verdict(file, &site, &view, report);
}

/// One resolved call parameter: the expected type when checkable plus the
/// display text for `TS2345` messages.
///
/// `expected` is `None` for accept-all (`any`, `unknown`) and uncheckable
/// (`object`, function, union) parameters: those skip per-argument (the non-literal
/// precedent), never decline whole calls, so decidable arity verdicts survive
/// uncheckable shapes. `optional` marks optional/defaulted positions, where
/// an explicit `undefined` argument is silent (the parameter's type carries
/// `| undefined` — probed tsc 7.0.2 P037); rest-element params always read
/// `false`, so `undefined` extras diagnose like any other mismatch.
#[derive(Clone, Debug)]
struct CallParam {
    /// Expected builtin [`TypeId`], or `None` when this position never
    /// mismatches.
    expected: Option<TypeId>,
    /// Parameter type text for `TS2345` messages (`"number"`, `"any"`,
    /// `"object"`, ...).
    display: String,
    /// Whether this position admits an explicit `undefined` argument.
    optional: bool,
}

/// One anchored call site for the shared verdict tail: direct calls anchor at
/// the callee identifier, member calls at the member identifier (mirroring
/// tsc's callee anchoring in both cases).
struct VerdictSite<'a> {
    /// Too-few-arity anchor (the callee or member identifier span).
    anchor: Span,
    /// Argument facts in source order.
    args: &'a [CallArg],
}

/// Admitted arity of one call target: `min` required arguments plus the
/// fixed `max` (`None` for rest-variadic lists, which admit any count past
/// `min`). Exact lists read `min == max`.
#[derive(Clone, Copy, Debug)]
struct CallArity {
    /// Fewest admitted arguments (the required prefix).
    min: usize,
    /// Most admitted fixed arguments (`None` when a rest element trails).
    max: Option<usize>,
}

/// One resolved call target for the shared verdict tail: fixed positions in
/// source order plus the arity they admit and, for rest lists, the element
/// type trailing extras check against.
struct CallTarget<'a> {
    /// Fixed positions in source order.
    fixed: &'a [CallParam],
    /// Admitted argument-count range.
    arity: CallArity,
    /// Rest-element expectation (`None` for exact/range lists).
    rest: Option<&'a CallParam>,
}

/// Emits at most one diagnostic for one anchored call site: arity
/// (`PITH2554`, or `PITH2555` below a rest minimum) beats argument types
/// (`PITH2345`), and only the first mismatched argument reports (all probed
/// on tsc 7.0.2 P014/P037).
///
/// Spans mirror the oracle: too-few arity at the anchor, too-many at the
/// first excess argument, arg-type at the mismatched argument. Exact lists
/// keep the historical `Expected 2 arguments …` spelling, ranges spell
/// `Expected 1-2 arguments …`, and rest minima spell
/// `Expected at least 1 arguments …`.
fn emit_call_verdict(
    file: FileId,
    site: &VerdictSite<'_>,
    target: &CallTarget<'_>,
    report: &mut FileReport,
) {
    let count = site.args.len();
    if count < target.arity.min {
        let (code, message) = if target.arity.max.is_none() {
            (
                CODE_ARITY_MIN,
                format!(
                    "Expected at least {} arguments, but got {count}.",
                    target.arity.min
                ),
            )
        } else {
            (
                CODE_ARITY,
                format!(
                    "Expected {} arguments, but got {count}.",
                    range_text(target.arity)
                ),
            )
        };
        report.diagnostics.push(PithDiagnostic {
            code: code.to_owned(),
            file,
            span: site.anchor,
            message,
        });
        return;
    }
    if let Some(max) = target.arity.max {
        if count > max {
            report.diagnostics.push(PithDiagnostic {
                code: CODE_ARITY.to_owned(),
                file,
                span: site.args[max].span,
                message: format!(
                    "Expected {} arguments, but got {count}.",
                    range_text(target.arity)
                ),
            });
            return;
        }
    }
    check_call_arguments(file, site, target, report);
}

/// Spells one admitted range-arity the way tsc does: `2` for exact lists,
/// `1-2` for ranges (rest minima never reach here — they spell `at least`).
fn range_text(arity: CallArity) -> String {
    match arity.max {
        Some(max) if max == arity.min => arity.min.to_string(),
        Some(max) => format!("{}-{max}", arity.min),
        None => format!("at least {}", arity.min),
    }
}

/// Checks supplied arguments positionally: fixed positions against their
/// params, trailing extras against the rest element (when one trails).
///
/// Assertion arguments evaluate first: complex casts skip per-argument (the
/// `NonLiteral` precedent — arity still enforces), declined casts diagnose
/// at the operand span, and admitted results check like their kind.
/// Declined casts never suppress the type check (probed tsc 7.0.2:
/// `sn(("hello" as number))` reports both `TS2345` and `TS2352`); the
/// first-mismatch rule still governs `TS2345`. Explicit `undefined` at an
/// optional position is silent (its type carries `| undefined` — probed
/// P037); everywhere else it diagnoses like any other mismatch.
fn check_call_arguments(
    file: FileId,
    site: &VerdictSite<'_>,
    target: &CallTarget<'_>,
    report: &mut FileReport,
) {
    for (index, argument) in site.args.iter().enumerate() {
        let param: &CallParam = if let Some(fixed) = target.fixed.get(index) {
            fixed
        } else if let Some(element) = target.rest {
            element
        } else {
            // No fixed position and no rest element: the arity gate above
            // already returned on every checked path, so this skips rather
            // than forcing a verdict.
            continue;
        };
        // Assertion arguments evaluate first: complex casts skip per-argument
        // (the `NonLiteral` precedent — arity still enforces), declined casts
        // diagnose at the operand span, and admitted results check like their
        // kind. Declined casts never suppress the type check (probed tsc
        // 7.0.2: `sn(("hello" as number))` reports both `TS2345` and
        // `TS2352`); the first-mismatch rule below still governs `TS2345`.
        let mut kind = argument.kind;
        if let Some(cast) = argument.cast.as_ref() {
            match evaluate_cast(cast) {
                CastEvaluation::Complex(_) => continue,
                CastEvaluation::Decline(result) => {
                    emit_cast_diagnostic(file, cast, &mut *report);
                    let Some(result_kind) = result.into_init() else {
                        continue;
                    };
                    kind = result_kind;
                }
                CastEvaluation::Admit(result) => {
                    let Some(result_kind) = result.into_init() else {
                        continue;
                    };
                    kind = result_kind;
                }
            }
        }
        if kind == InitKind::NonLiteral {
            continue;
        }
        if kind == InitKind::Undefined && param.optional {
            continue;
        }
        let Some(expected) = param.expected else {
            continue;
        };
        let display = param.display.as_str();
        if kind.type_id() != expected {
            report.diagnostics.push(PithDiagnostic {
                code: CODE_ARG_TYPE.to_owned(),
                file,
                span: argument.span,
                message: format!(
                    "Argument of type '{}' is not assignable to parameter of type '{display}'.",
                    kind.name(),
                ),
            });
            return;
        }
    }
}

/// One admitted parameter list for [`check_one_call`]: fixed positions in
/// source order (each an `(expected, display, optional)` triple — `None`
/// expectations are accept-all `any`/`unknown`), the admitted
/// argument-count range, and the rest-element type when variadic.
struct ResolvedCallParams {
    /// Fixed positions in source order: expected type, display text, and
    /// whether explicit `undefined` is silent at the position.
    fixed: Vec<(Option<TypeId>, String, bool)>,
    /// Fewest admitted arguments (the required prefix).
    min: usize,
    /// Most admitted fixed arguments (`None` when a rest element trails).
    max: Option<usize>,
    /// Rest-element expectation (`None` for exact/range lists).
    rest: Option<(Option<TypeId>, String)>,
}

/// Gates one call's parameter list for [`check_single_call`].
///
/// `Some` carries the admitted range plus per-position expectations (see
/// [`ResolvedCallParams`]); `None` means one [`UnsupportedDecl`] was pushed
/// at the callee span and the call declines.
fn call_params(
    call: &CallSite,
    decl: &FunctionDecl,
    file: FileId,
    report: &mut FileReport,
) -> Option<ResolvedCallParams> {
    match resolve_params(decl) {
        Ok(resolved) => Some(resolved),
        Err(reason) => {
            decline(call, file, report, &reason);
            None
        }
    }
}

/// Resolves one declaration's parameter list into its admitted call shape.
///
/// `Ok` carries the range plus per-position expectations (see
/// [`ResolvedCallParams`]); `Err` carries the bare decline reason.
/// Structural gates run first (`params_complex`, non-trailing rest), then
/// parameter-by-parameter in order (unannotated, required-after-optional,
/// then the type text): the first failure wins, so reasons stay single and
/// deterministic. Overload resolution reuses this per signature, so generic
/// signatures gate separately (see [`check_overload_call`]) rather than
/// here.
fn resolve_params(decl: &FunctionDecl) -> Result<ResolvedCallParams, String> {
    if decl.params_complex {
        return Err("non-identifier parameter pattern is outside the subset".to_owned());
    }
    if let Some(trailing) = decl
        .params
        .iter()
        .position(|param| param.is_rest)
        .filter(|index| index.saturating_add(1) != decl.params.len())
    {
        return Err(format!(
            "rest parameter '{}' must be last: trailing positions are outside the subset",
            decl.params[trailing].name
        ));
    }
    let mut fixed = Vec::with_capacity(decl.params.len());
    let mut rest: Option<(Option<TypeId>, String)> = None;
    let mut seen_optional = false;
    for param in &decl.params {
        if !param.annotated {
            return Err(format!(
                "unannotated parameter '{}' is outside the subset",
                param.name
            ));
        }
        if param.is_rest {
            rest = Some(classify_rest_element(param)?);
            continue;
        }
        if param.optional {
            seen_optional = true;
        } else if seen_optional {
            return Err(format!(
                "required parameter '{}' follows an optional parameter: \
                required-after-optional shapes are outside the subset",
                param.name
            ));
        }
        match classify_param(param) {
            Ok((expected, display)) => fixed.push((expected, display, param.optional)),
            Err(reason) => return Err(reason),
        }
    }
    let min = fixed.iter().filter(|member| !member.2).count();
    let max = if rest.is_some() {
        None
    } else {
        Some(fixed.len())
    };
    Ok(ResolvedCallParams {
        fixed,
        min,
        max,
        rest,
    })
}

/// Pushes one call-site [`UnsupportedDecl`] at the callee span.
fn decline(call: &CallSite, file: FileId, report: &mut FileReport, reason: &str) {
    report.unsupported.push(UnsupportedDecl {
        file,
        span: call.callee_span,
        reason: format!("call to '{}': {reason}", call.callee),
    });
}

/// One resolved call target with owned positions for the shared verdict
/// tail: [`ResolvedCallParams`] moved into [`CallParam`]s plus the admitted
/// range, so overload attempts (which reuse one target across the arity and
/// type phases) and [`check_single_call`] share one construction.
struct OwnedTarget {
    /// Fixed positions in source order.
    fixed: Vec<CallParam>,
    /// Fewest admitted arguments (the required prefix).
    min: usize,
    /// Most admitted fixed arguments (`None` when a rest element trails).
    max: Option<usize>,
    /// Rest-element expectation (`None` for exact/range lists).
    rest: Option<CallParam>,
}

/// Moves one resolved parameter list into an [`OwnedTarget`].
fn owned_target(resolved: ResolvedCallParams) -> OwnedTarget {
    let fixed = resolved
        .fixed
        .into_iter()
        .map(|(expected, display, optional)| CallParam {
            expected,
            display,
            optional,
        })
        .collect();
    let rest = resolved.rest.map(|(expected, display)| CallParam {
        expected,
        display,
        optional: false,
    });
    OwnedTarget {
        fixed,
        min: resolved.min,
        max: resolved.max,
        rest,
    }
}

/// Mutable checking state for one [`check_overload_call`] run, bundled so
/// the per-phase helpers stay lean (pedantic arity discipline, mirroring
/// [`MemberRun`]).
struct OverloadRun<'a> {
    file: FileId,
    decls: &'a [FunctionDecl],
    call: &'a CallSite,
    report: &'a mut FileReport,
}

/// One checkable overload signature: its resolved parameter list, in source
/// order (the last entry elaborates `TS2769`).
struct OverloadCandidate {
    /// The admitted range plus per-position expectations.
    resolved: ResolvedCallParams,
}

/// One first-mismatch inside an overload attempt: the offending argument
/// span plus the oracle's `TS2345`-shaped elaboration pieces.
struct OverloadMismatch {
    /// Span of the mismatched argument (the oracle anchor).
    span: Span,
    /// Widened actual-type name (`'boolean'`, `'number'`, ...).
    actual: &'static str,
    /// Expected parameter-type text (`'number'`, `'string'`, ...).
    display: String,
}

/// Checks one call site against several same-name declarations, pushing
/// into the run report (probed tsc 7.0.2 `--strict --pretty false`; probes
/// in `.agent/scratch/p044-probes/`, rules in the module docs).
///
/// At most one diagnostic ever fires per call; declines push exactly one
/// [`UnsupportedDecl`]. Outcomes, in order:
///
/// - More than one declaration carries a body (shadowing, not overloads):
///   one [`UnsupportedDecl`] — implementations cannot be disambiguated.
/// - Generic signatures and signatures [`resolve_params`] rejects (union,
///   object, conditional, or unknown parameter types, one at a time) are
///   excluded with their own reasons: if any remaining signature admits the
///   call the site is clean (sound: the oracle checks a superset), else one
///   [`UnsupportedDecl`] records every exclusion — never a forced verdict.
/// - Otherwise every signature is checkable and the call resolves by
///   any-match (see [`resolve_overload`]).
fn check_overload_call(run: &mut OverloadRun<'_>, candidates: &[usize]) {
    let bodies = candidates
        .iter()
        .filter(|index| !matches!(run.decls[**index].body, FunctionBody::NoBody { .. }))
        .count();
    if bodies > 1 {
        run.report.unsupported.push(UnsupportedDecl {
            file: run.file,
            span: run.call.callee_span,
            reason: format!(
                "multiple declarations with bodies for '{}': shadowing is outside the subset",
                run.call.callee
            ),
        });
        return;
    }
    let mut checkable: Vec<OverloadCandidate> = Vec::with_capacity(candidates.len());
    let mut excluded: Vec<String> = Vec::new();
    for index in candidates {
        let decl = &run.decls[*index];
        if !matches!(decl.body, FunctionBody::NoBody { .. }) {
            continue;
        }
        if decl.has_type_params {
            excluded.push(
                "overload signature with generic type parameters is outside the subset".to_owned(),
            );
            continue;
        }
        match resolve_params(decl) {
            Ok(resolved) => checkable.push(OverloadCandidate { resolved }),
            Err(reason) => excluded.push(reason),
        }
    }
    // Cast pre-evaluation emits `TS2352` exactly once per call, before any
    // arity verdict (probed tsc 7.0.2 P044 `m15`); every path below reuses
    // these kinds and never re-evaluates.
    let kinds = effective_arg_kinds(run.file, run.call, run.report);
    if !excluded.is_empty() {
        let clean = checkable
            .iter()
            .any(|candidate| overload_matches(&candidate.resolved, &kinds));
        if !clean {
            let checkable_note = if checkable.is_empty() {
                String::new()
            } else {
                format!("; {} checkable fail", checkable.len())
            };
            let detail = format!("excluded: {}{checkable_note}", excluded.join("; "));
            run.report.unsupported.push(UnsupportedDecl {
                file: run.file,
                span: run.call.callee_span,
                reason: format!(
                    "call to '{}': no overload signature admits this call ({detail})",
                    run.call.callee
                ),
            });
        }
        return;
    }
    if checkable.len() == 1 {
        let Some(candidate) = checkable.pop() else {
            // Unreachable: the length check guarantees one entry. Decline
            // instead of forcing a verdict.
            run.report.unsupported.push(UnsupportedDecl {
                file: run.file,
                span: run.call.callee_span,
                reason: format!(
                    "call to '{}': no overload signature admits this call",
                    run.call.callee
                ),
            });
            return;
        };
        check_resolved_call(run, candidate.resolved, &kinds);
        return;
    }
    resolve_overload(run, &checkable, &kinds);
}

/// Checks one resolved signature inside an overload group through the
/// shared verdict tail, over cast-pre-evaluated argument kinds (so `TS2352`
/// diagnostics fire exactly once per call, before any arity verdict — the
/// probed `m15` order).
fn check_resolved_call(
    run: &mut OverloadRun<'_>,
    resolved: ResolvedCallParams,
    kinds: &[Option<InitKind>],
) {
    let target = owned_target(resolved);
    let synth: Vec<CallArg> = run
        .call
        .args
        .iter()
        .zip(kinds.iter())
        .map(|(argument, kind)| CallArg {
            kind: kind.unwrap_or(InitKind::NonLiteral),
            span: argument.span,
            cast: None,
        })
        .collect();
    let site = VerdictSite {
        anchor: run.call.callee_span,
        args: &synth,
    };
    let view = CallTarget {
        fixed: &target.fixed,
        arity: CallArity {
            min: target.min,
            max: target.max,
        },
        rest: target.rest.as_ref(),
    };
    emit_call_verdict(run.file, &site, &view, run.report);
}

/// Resolves one call against two or more checkable overload signatures by
/// any-match (probed tsc 7.0.2 P044): the call is clean when ANY signature
/// admits it, whatever the order; otherwise exactly one diagnostic fires —
/// `TS2554`/`TS2555` when no signature admits the count (union range, or
/// the gap spelling `TS2575`), else `TS2769` elaborating the last
/// signature's first mismatch.
fn resolve_overload(
    run: &mut OverloadRun<'_>,
    checkable: &[OverloadCandidate],
    kinds: &[Option<InitKind>],
) {
    let count = run.call.args.len();
    let compatible: Vec<usize> = checkable
        .iter()
        .enumerate()
        .filter(|(_, candidate)| arity_admits(&candidate.resolved, count))
        .map(|(index, _)| index)
        .collect();
    if compatible.is_empty() {
        emit_no_compatible(run, checkable, count);
        return;
    }
    if compatible.len() == 1 {
        let resolved = single_compatible(&checkable[compatible[0]]);
        check_resolved_call(run, resolved, kinds);
        return;
    }
    let clean = compatible
        .iter()
        .any(|index| overload_matches(&checkable[*index].resolved, kinds));
    if clean {
        return;
    }
    let Some(last) = compatible.last() else {
        return;
    };
    let Some(mismatch) = first_overload_mismatch(&checkable[*last].resolved, run.call, kinds)
    else {
        return;
    };
    run.report.diagnostics.push(PithDiagnostic {
        code: CODE_OVERLOAD.to_owned(),
        file: run.file,
        span: mismatch.span,
        message: format!(
            "No overload matches this call.\n  The last overload gave the following error.\n    \
            Argument of type '{}' is not assignable to parameter of type '{}'.",
            mismatch.actual, mismatch.display
        ),
    });
}

/// Copies one compatible overload signature's resolved parameter list
/// (borrowed candidates cannot move theirs out).
fn single_compatible(candidate: &OverloadCandidate) -> ResolvedCallParams {
    ResolvedCallParams {
        fixed: candidate.resolved.fixed.clone(),
        min: candidate.resolved.min,
        max: candidate.resolved.max,
        rest: candidate.resolved.rest.clone(),
    }
}

/// Whether one resolved signature admits an argument count (the range gate
/// of [`emit_call_verdict`], without diagnostics).
fn arity_admits(resolved: &ResolvedCallParams, count: usize) -> bool {
    if count < resolved.min {
        return false;
    }
    match resolved.max {
        Some(max) => count <= max,
        None => true,
    }
}

/// Whether one resolved signature admits a call with pre-evaluated
/// argument kinds: the count in range, and every checkable position equal
/// (non-literal and complex-cast positions skip, accept-all parameters
/// never mismatch, explicit `undefined` at optional positions is silent —
/// the [`check_call_arguments`] precedents, without diagnostics).
fn overload_matches(resolved: &ResolvedCallParams, kinds: &[Option<InitKind>]) -> bool {
    arity_admits(resolved, kinds.len()) && first_overload_mismatch_inner(resolved, kinds).is_none()
}

/// Finds the first type mismatch of one resolved signature over
/// pre-evaluated argument kinds, or `None` when every checkable position
/// agrees (arity unchecked — callers gate counts separately).
fn first_overload_mismatch_inner(
    resolved: &ResolvedCallParams,
    kinds: &[Option<InitKind>],
) -> Option<(usize, &'static str, String)> {
    for (index, kind) in kinds.iter().enumerate() {
        let Some(kind) = kind else {
            continue;
        };
        let (expected, display, optional) = if let Some(fixed) = resolved.fixed.get(index) {
            (fixed.0, fixed.1.as_str(), fixed.2)
        } else if let Some(element) = resolved.rest.as_ref() {
            (element.0, element.1.as_str(), false)
        } else {
            continue;
        };
        if *kind == InitKind::Undefined && optional {
            continue;
        }
        let Some(expected) = expected else {
            continue;
        };
        if kind.type_id() != expected {
            return Some((index, kind.name(), display.to_owned()));
        }
    }
    None
}

/// Finds the first type mismatch of one resolved signature at a call site,
/// pairing the inner mismatch with the mismatched argument's span (the
/// oracle anchor).
fn first_overload_mismatch(
    resolved: &ResolvedCallParams,
    call: &CallSite,
    kinds: &[Option<InitKind>],
) -> Option<OverloadMismatch> {
    let (index, actual, display) = first_overload_mismatch_inner(resolved, kinds)?;
    Some(OverloadMismatch {
        span: call.args[index].span,
        actual,
        display,
    })
}

/// Emits the no-arity-compatible diagnostic for an overload call: below the
/// union minimum the `TS2554` range (or `TS2555` below a rest minimum, the
/// [`emit_call_verdict`] spellings) at the callee; past the union maximum
/// `TS2554` at the first excess argument; strictly between, the gap
/// spelling `TS2575` naming the nearest signature minimums below and above
/// (all probed tsc 7.0.2 P044).
fn emit_no_compatible(run: &mut OverloadRun<'_>, checkable: &[OverloadCandidate], count: usize) {
    let file = run.file;
    let anchor = run.call.callee_span;
    let (min_union, max_union) = union_arity(checkable);
    if count < min_union {
        let (code, message) = if max_union.is_none() {
            (
                CODE_ARITY_MIN,
                format!("Expected at least {min_union} arguments, but got {count}."),
            )
        } else {
            (
                CODE_ARITY,
                format!(
                    "Expected {} arguments, but got {count}.",
                    range_text(CallArity {
                        min: min_union,
                        max: max_union,
                    })
                ),
            )
        };
        run.report.diagnostics.push(PithDiagnostic {
            code: code.to_owned(),
            file,
            span: anchor,
            message,
        });
        return;
    }
    if let Some(max) = max_union {
        if count > max {
            run.report.diagnostics.push(PithDiagnostic {
                code: CODE_ARITY.to_owned(),
                file,
                span: run.call.args[max].span,
                message: format!(
                    "Expected {} arguments, but got {count}.",
                    range_text(CallArity {
                        min: min_union,
                        max: max_union,
                    })
                ),
            });
            return;
        }
    }
    let Some((lo, hi)) = gap_bounds(checkable, count) else {
        run.report.unsupported.push(UnsupportedDecl {
            file,
            span: anchor,
            reason: format!(
                "call to '{}': no overload signature admits {count} arguments",
                run.call.callee
            ),
        });
        return;
    };
    run.report.diagnostics.push(PithDiagnostic {
        code: CODE_OVERLOAD_ARITY.to_owned(),
        file,
        span: anchor,
        message: format!(
            "No overload expects {count} arguments, but overloads do exist that expect either \
            {lo} or {hi} arguments."
        ),
    });
}

/// The union admitted count of several checkable signatures: the minimum of
/// their minimums plus the maximum of their maximums (`None` when any rest
/// signature trails — too-many is then inadmissible, exactly like
/// [`emit_call_verdict`]).
fn union_arity(checkable: &[OverloadCandidate]) -> (usize, Option<usize>) {
    let min_union = checkable
        .iter()
        .map(|candidate| candidate.resolved.min)
        .min()
        .unwrap_or(0);
    let max_union = if checkable
        .iter()
        .any(|candidate| candidate.resolved.max.is_none())
    {
        None
    } else {
        checkable
            .iter()
            .filter_map(|candidate| candidate.resolved.max)
            .max()
    };
    (min_union, max_union)
}

/// The nearest distinct signature minimums below and above an
/// admitted-by-none count (probed tsc 7.0.2 P044: ranges contribute their
/// minimum, e.g. `1-2` plus `5` names `1` and `5`). `None` when either side
/// is missing (unreachable in the gap branch — the caller declines instead
/// of forcing a verdict).
fn gap_bounds(checkable: &[OverloadCandidate], count: usize) -> Option<(usize, usize)> {
    let mut mins: Vec<usize> = checkable
        .iter()
        .map(|candidate| candidate.resolved.min)
        .collect();
    mins.sort_unstable();
    mins.dedup();
    let lo = mins.iter().rev().find(|min| **min < count).copied()?;
    let hi = mins.iter().find(|min| **min > count).copied()?;
    Some((lo, hi))
}

/// Pre-evaluates assertion arguments once per overload call: `None` marks
/// positions matching never fails (non-literal arguments, complex casts,
/// and boundary (`any`/`unknown`/`never`) cast results — the
/// [`check_call_arguments`] precedents). Declined casts diagnose `TS2352`
/// at the operand span exactly once, before any arity verdict (probed tsc
/// 7.0.2 P044 `m14`/`m15`); admitted results check like their kind.
fn effective_arg_kinds(
    file: FileId,
    call: &CallSite,
    report: &mut FileReport,
) -> Vec<Option<InitKind>> {
    let mut kinds = Vec::with_capacity(call.args.len());
    for argument in &call.args {
        let Some(cast) = argument.cast.as_ref() else {
            kinds.push(if argument.kind == InitKind::NonLiteral {
                None
            } else {
                Some(argument.kind)
            });
            continue;
        };
        match evaluate_cast(cast) {
            CastEvaluation::Complex(_) => kinds.push(None),
            CastEvaluation::Decline(result) => {
                emit_cast_diagnostic(file, cast, report);
                kinds.push(result.into_init());
            }
            CastEvaluation::Admit(result) => kinds.push(result.into_init()),
        }
    }
    kinds
}

/// Classifies one annotated rest parameter into its element `(expected,
/// display)`: only array spellings with a primitive-or-boundary element
/// admit (`any`/`unknown` elements accept every extra silently, mirroring
/// the array-element rule; `never` keeps its diagnosing expectation, the
/// same precedent).
///
/// `Err` carries the decline reason: non-array types mirror tsc's `TS2370`
/// (`A rest parameter must be of an array type.`) as a decline — the solver
/// spells no declaration diagnostics — and uncheckable element shapes reuse
/// the array classifier's reasons, prefixed with the parameter name.
fn classify_rest_element(param: &FunctionParam) -> Result<(Option<TypeId>, String), String> {
    let text = param.annotation.as_deref().map_or("", str::trim);
    let Some(array) = classify_array_annotation(text) else {
        return Err(format!(
            "rest parameter '{}' must be of an array type: outside the subset",
            param.name
        ));
    };
    match array {
        ArrayAnnotation::Decline(reason) => {
            Err(format!("rest parameter '{}': {reason}", param.name))
        }
        ArrayAnnotation::Admit(element) => {
            if element.id == TypeStore::ANY || element.id == TypeStore::UNKNOWN {
                Ok((None, element.spelling.to_owned()))
            } else {
                Ok((Some(element.id), element.spelling.to_owned()))
            }
        }
    }
}
/// Classifies one annotated fixed parameter into its
/// expected ([`TypeId`], display text): `Err` carries the decline reason
/// (union, object, unknown, or missing type text the subset cannot spell
/// argument checks against).
///
/// `any` and `unknown` parameters accept every literal (probed tsc 7.0.2:
/// both directions silent), so they classify accept-all (`None`, the
/// non-literal precedent); `never` keeps declining (unprobed message shape
/// — never forced).
fn classify_param(param: &FunctionParam) -> Result<(Option<TypeId>, String), String> {
    let text = param.annotation.as_deref().map_or("", str::trim);
    if text.contains('|') {
        return Err(format!(
            "union parameter type '{text}' is outside the subset"
        ));
    }
    if matches!(
        boundary_annotation_type(text),
        Some(id) if id == TypeStore::ANY || id == TypeStore::UNKNOWN
    ) {
        return Ok((None, text.to_owned()));
    }
    annotation_type(text).map_or_else(
        || {
            Err(format!(
                "parameter type '{text}' for '{}' is outside the subset",
                param.name
            ))
        },
        |expected| Ok((Some(expected), text.to_owned())),
    )
}

/// One `JSON.parse(...)`-shaped member call site to check.
///
/// Fact-fed from the adapter's `MemberCallFact`: receiver and member names
/// plus the member identifier span, the whole call span, and one [`CallArg`]
/// per argument in source order (only the literal-kind enum mapping is
/// driver-side, mechanical and exhaustive).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemberCallSite {
    /// Receiver name as written (`JSON` above).
    pub receiver: String,
    /// Member name as written (`parse` above).
    pub member: String,
    /// Span of the member identifier (too-few-arity anchor, mirroring tsc).
    pub member_span: Span,
    /// Span of the whole call expression.
    pub span: Span,
    /// Argument facts in source order.
    pub args: Vec<CallArg>,
}

/// One opaque lib signature: an exact arity plus one [`CallParam`] per
/// position in source order.
///
/// Only fixed-arity members with primitive-or-`any` parameters live here (see
/// [`opaque_signature`]); ranges, overloads, and variadics decline per site
/// with lib reasons instead of forcing verdicts.
#[derive(Clone, Debug)]
struct OpaqueSig {
    /// Exact accepted argument count.
    arity: usize,
    /// Per-position expectations (`None` positions never mismatch).
    params: Vec<CallParam>,
}

/// Builds one exact-arity opaque signature from per-position
/// `(expected, display)` pairs.
fn exact_sig(arity: usize, params: &[(Option<TypeId>, &str)]) -> OpaqueSig {
    let mut out = Vec::with_capacity(params.len());
    for (expected, display) in params {
        out.push(CallParam {
            expected: *expected,
            display: (*display).to_owned(),
            optional: false,
        });
    }
    OpaqueSig { arity, params: out }
}

/// Whether a receiver names a known value with opaque lib signatures.
///
/// Mirrors the adapter's `pith_frontend::is_known_value_receiver` gate
/// (kept as a local match: `pith-solver` takes no runtime dependency on
/// `pith-frontend` by boundary law, dev-dependencies aside).
#[must_use]
fn is_known_value_receiver(name: &str) -> bool {
    matches!(name, "JSON" | "Object" | "Array" | "console" | "Math")
}

/// Resolves one allowlisted member to its opaque signature, or `None` when
/// the member is unknown or known-but-uncheckable (see
/// [`member_shape_decline`]).
///
/// Every entry is probe-grounded on tsc 7.0.2 (see the module-level P024
/// record): single-number `Math` members plus `pow`/`atan2` check fully,
/// `Array.isArray` checks arity with an accept-all parameter, and
/// `Object.keys` checks arity with an uncheckable `object` parameter.
fn opaque_signature(receiver: &str, member: &str) -> Option<OpaqueSig> {
    match (receiver, member) {
        ("Array", "isArray") => Some(exact_sig(1, &[(None, "any")])),
        ("Object", "keys") => Some(exact_sig(1, &[(None, "object")])),
        ("Math", "floor" | "ceil" | "round" | "trunc" | "abs" | "sqrt" | "cbrt") => {
            Some(exact_sig(1, &[(Some(TypeStore::NUMBER), "number")]))
        }
        ("Math", "pow" | "atan2") => {
            let number = (Some(TypeStore::NUMBER), "number");
            Some(exact_sig(2, &[number, number]))
        }
        _ => None,
    }
}

/// Names the lib reason for one known-but-uncheckable member, or `None` when
/// the member is unknown (the caller declines those separately).
///
/// Every entry is probe-grounded on tsc 7.0.2: `JSON.parse` spells a `1-2`
/// range arity and a function-typed reviver, `JSON.stringify` spells
/// `TS2769` overloads, and `console` methods plus `Math.max/min` accept any
/// argument count (variadic, the rest-arg precedent).
fn member_shape_decline(receiver: &str, member: &str) -> Option<&'static str> {
    match (receiver, member) {
        ("JSON", "parse") => Some("takes a range of arities (1-2 arguments), outside the subset"),
        ("JSON", "stringify") => Some("overload resolution is outside the subset"),
        ("console", "warn" | "log" | "error") => {
            Some("takes variadic arguments, outside the subset")
        }
        ("Math", "max" | "min") => Some("takes variadic arguments, outside the subset"),
        _ => None,
    }
}

/// Mutable checking state for one [`check_member_calls`] run, bundled so the
/// per-site helper stays lean (pedantic arity discipline, mirroring
/// [`ClassRun`]).
struct MemberRun<'a> {
    file: FileId,
    binder: &'a Binder,
    report: &'a mut FileReport,
}

/// Checks every member call site in `calls` against the opaque lib table for
/// `file`, returning the sorted [`FileReport`].
///
/// Member calls never resolve against user declarations: known receivers
/// route through [`opaque_signature`] into the shared [`emit_call_verdict`]
/// tail (one family per site, arity first, first mismatch only), and every
/// other shape declines or skips, never verdicts. Per-site outcomes, in
/// order:
///
/// - Unknown receiver: names already tracked as unresolved references skip
///   silently (the [`check_calls`] precedent — diagnosing would
///   double-report one signal); untracked names decline as driver skew.
/// - Known receiver with an opaque signature: the shared verdict tail.
/// - Known receiver with an uncheckable shape ([`member_shape_decline`]):
///   one [`UnsupportedDecl`] with the lib reason.
/// - Known receiver with an unknown member: one [`UnsupportedDecl`] naming
///   the member (full lib types are outside the subset).
///
/// Spans mirror the oracle through the member identifier: declines anchor at
/// [`MemberCallSite::member_span`], verdicts through [`VerdictSite`].
#[must_use]
pub fn check_member_calls(file: FileId, calls: &[MemberCallSite], binder: &Binder) -> FileReport {
    let mut report = FileReport::default();
    let mut run = MemberRun {
        file,
        binder,
        report: &mut report,
    };
    for call in calls {
        check_one_member_call(&mut run, call);
    }
    sort_report(run.report);
    std::mem::take(run.report)
}

/// Checks one member call site, pushing into the run report.
///
/// At most one diagnostic ever fires per call (arity before types, first
/// mismatch only, via [`emit_call_verdict`]); declines push exactly one
/// [`UnsupportedDecl`].
fn check_one_member_call(run: &mut MemberRun<'_>, call: &MemberCallSite) {
    if !is_known_value_receiver(call.receiver.as_str()) {
        if run
            .binder
            .unresolved()
            .iter()
            .any(|entry| entry.file == run.file && entry.name == call.receiver)
        {
            // Tracked as an unresolved reference already: skip, never
            // double-diagnose (the direct-call precedent).
            return;
        }
        run.report.unsupported.push(UnsupportedDecl {
            file: run.file,
            span: call.member_span,
            reason: format!(
                "member call on undeclared receiver '{}': nothing to check against",
                call.receiver
            ),
        });
        return;
    }
    if let Some(sig) = opaque_signature(call.receiver.as_str(), call.member.as_str()) {
        // Constructor-built tables keep arity and positions in lockstep; the
        // shared tail enforces `params.len()`, so this pins coherence.
        debug_assert_eq!(sig.arity, sig.params.len());
        let site = VerdictSite {
            anchor: call.member_span,
            args: &call.args,
        };
        let target = CallTarget {
            fixed: &sig.params,
            arity: CallArity {
                min: sig.arity,
                max: Some(sig.arity),
            },
            rest: None,
        };
        emit_call_verdict(run.file, &site, &target, &mut *run.report);
        return;
    }
    if let Some(reason) = member_shape_decline(call.receiver.as_str(), call.member.as_str()) {
        decline_member(run, call, reason);
        return;
    }
    decline_member(
        run,
        call,
        &format!(
            "unknown member '{}' on known value '{}': full lib types are outside the subset",
            call.member, call.receiver
        ),
    );
}

/// Pushes one member-site [`UnsupportedDecl`] at the member span.
fn decline_member(run: &mut MemberRun<'_>, call: &MemberCallSite, reason: &str) {
    run.report.unsupported.push(UnsupportedDecl {
        file: run.file,
        span: call.member_span,
        reason: format!("member call '{}.{}': {reason}", call.receiver, call.member),
    });
}

/// One class property: annotation plus initializer shapes for a synthetic
/// const declaration.
///
/// Driver-mapped from the adapter's `ClassPropFact` (mechanical field copy).
/// `complex_reason` carries the adapter's decline marker verbatim; checkable
/// properties carry the raw annotation text plus the literal initializer for
/// [`check_one`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassProp {
    /// Property name as written (feeds the dotted synthetic-decl name only;
    /// never resolved — see [`check_classes`]).
    pub name: String,
    /// Span of the property definition (diagnostic anchor and decl fallback).
    pub span: Span,
    /// Raw annotation text (`Some("number")`); `None` when unannotated.
    pub annotation: Option<String>,
    /// Initializer literal kind; `None` means no initializer.
    pub init: Option<InitKind>,
    /// Object-literal members when the value is a representable `{ ... }`;
    /// `None` otherwise.
    pub init_object: Option<ObjectInit>,
    /// Adapter decline marker; `Some` means the property declines.
    pub complex_reason: Option<String>,
}

/// One `class Name { ... }` declaration to check.
///
/// Driver-mapped from the adapter's `ClassFact` (mechanical field copies,
/// plus the binder [`SymbolId`] resolved from the same [`Binder`] used for
/// checking). Properties check through synthetic [`ConstDecl`]s; the
/// constructor feeds synthetic [`FunctionDecl`]s for [`check_one_call`];
/// every out-of-subset family declines with a class-level reason (see the
/// module-level class rules).
/// Whole-declaration form of one `class`: expression, abstract, and declare
/// markers travel together (at most three flags, so the struct stays lean).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ClassForm {
    /// `true` for class expressions.
    pub is_expression: bool,
    /// `true` for `abstract class`.
    pub is_abstract: bool,
    /// `true` for `declare class` (ambient, never instantiated here).
    pub is_declare: bool,
}

/// One out-of-subset family present on a class declaration, mirroring the
/// adapter's [`ClassFamily`](pith_frontend::ClassFamily) facts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassFamily {
    /// Any non-constructor instance method.
    Methods,
    /// Any `accessor` property or getter/setter.
    Accessors,
    /// Any `extends` clause or `implements` list.
    Heritage,
    /// Any static member (properties, methods, blocks).
    Statics,
    /// Decorators on the class or any member.
    Decorators,
    /// Computed or non-identifier, non-`#private` keys.
    Computed,
    /// Any index signature.
    IndexSignature,
    /// Any `this`-member write in a method, constructor, or static block.
    ThisAssignments,
}

impl ClassFamily {
    /// The decline reason for one family on `class`, mirroring the
    /// long-standing per-family notes.
    fn reason(self, class: &str) -> String {
        match self {
            Self::Methods => format!(
                "methods on class '{class}': method bodies are unchecked, outside the subset"
            ),
            Self::Accessors => {
                format!("accessors on class '{class}' are outside the subset")
            }
            Self::Heritage => format!(
                "heritage clause on class '{class}' (extends/implements) is outside the subset"
            ),
            Self::Statics => {
                format!("static members on class '{class}' are outside the subset")
            }
            Self::Decorators => {
                format!("decorators on class '{class}' are outside the subset")
            }
            Self::Computed => {
                format!("computed or non-identifier keys on class '{class}' are outside the subset")
            }
            Self::IndexSignature => {
                format!("index signatures on class '{class}' are outside the subset")
            }
            Self::ThisAssignments => format!(
                "this-assignments in class '{class}' are outside the subset (no flow facts)"
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassDecl {
    /// Class name as written.
    pub name: String,
    /// Fallback span, used only when neither `symbol` nor scope-sensitive
    /// resolution finds the declaration in the [`Binder`].
    pub span: Span,
    /// Per-file scope index of the declaration (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity when the driver resolved it (preferred over
    /// scope-sensitive lookup); must come from the same `file`/`Binder`.
    pub symbol: Option<SymbolId>,
    /// Instance property facts in source order.
    pub properties: Vec<ClassProp>,
    /// Constructor identifier parameters in source order (empty for the
    /// implicit constructor).
    pub ctor_params: Vec<FunctionParam>,
    /// `true` when the constructor holds an unrepresentable pattern: `new`
    /// sites decline per site through [`check_one_call`].
    pub ctor_complex: bool,
    /// `true` when overloads leave no single parameter list: the class
    /// declines constructor checking with one note while properties still
    /// check (and `new` sites skip silently — the note covers them).
    pub ctor_overloads: bool,
    /// Out-of-subset families present on the declaration, in first-seen
    /// order without duplicates (one note per family).
    pub declined: Vec<ClassFamily>,
    /// Whole-declaration form markers.
    pub form: ClassForm,
    /// Declared type parameters (generic classes check nothing: `T`
    /// positions would otherwise mis-diagnose `TS2304`).
    pub has_type_params: bool,
}

/// One `new C(...)` construction site to check.
///
/// Driver-mapped from the adapter's `NewFact` (mechanical field copy, only
/// the literal-kind enum mapping is driver-side). Routes through
/// [`check_one_call`] against the synthetic constructor declaration, so
/// arity/argument verdicts match function calls by construction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NewSite {
    /// Class name as written.
    pub class_name: String,
    /// Span of the class-name identifier (too-few-arity anchor, mirroring
    /// tsc).
    pub callee_span: Span,
    /// Span of the whole `new` expression.
    pub span: Span,
    /// Argument facts in source order.
    pub args: Vec<CallArg>,
}

/// Mutable checking state for one [`check_classes`] run, bundled so the
/// per-class helpers stay lean (pedantic arity discipline, mirroring
/// [`GenericCallCtx`]).
struct ClassRun<'a, 'b> {
    file: FileId,
    binder: &'a Binder,
    db: &'a mut QueryDb,
    /// Running synthetic-declaration counter for disjoint occurrence nodes
    /// (see [`class_occurrence_node`]).
    occurrence: u32,
    /// Synthetic constructor declarations for `new`-site checking (one per
    /// checkable class, in class order).
    synth: Vec<FunctionDecl>,
    /// Names whose constructors declined at declaration level (overloads,
    /// generics, abstract/declare/expression forms): `new` sites against
    /// them skip silently — the declaration note covers them (the P016
    /// precedent).
    excluded: Vec<&'b str>,
    report: &'a mut FileReport,
}

/// Checks every class declaration in `decls` plus every construction site in
/// `news` for `file`, returning the sorted [`FileReport`].
///
/// Per-class outcomes, in order: whole-declaration declines (expressions,
/// abstract/declare forms, generics — one note, properties and `new` sites
/// both skip); property checks through synthetic [`ConstDecl`]s (one verdict
/// or decline per property, exactly the const path); one class-level note
/// per remaining out-of-subset family (methods, accessors, heritage,
/// statics, decorators, computed keys, index signatures, `this`-assignments,
/// constructor overloads); then the constructor joins the synthetic call set
/// (implicit constructors take 0 arguments). `new` sites route through
/// [`check_one_call`], so per-site arity/argument verdicts, overload
/// declines, and unresolved-callee silence all mirror function calls —
/// except sites against declaration-declined constructors, which skip
/// silently under their declaration note.
#[must_use]
pub fn check_classes(
    file: FileId,
    decls: &[ClassDecl],
    news: &[NewSite],
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    let mut report = FileReport::default();
    let mut run = ClassRun {
        file,
        binder,
        db: &mut *db,
        occurrence: 0,
        synth: Vec::with_capacity(decls.len()),
        excluded: Vec::new(),
        report: &mut report,
    };
    for decl in decls {
        check_one_class(decl, &mut run);
    }
    let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
    for (index, decl) in run.synth.iter().enumerate() {
        by_name.entry(decl.name.as_str()).or_default().push(index);
    }
    for site in news {
        if !by_name.contains_key(site.class_name.as_str())
            && run.excluded.contains(&site.class_name.as_str())
        {
            continue;
        }
        let call = CallSite {
            callee: site.class_name.clone(),
            callee_span: site.callee_span,
            span: site.span,
            args: site.args.clone(),
        };
        check_one_call(
            run.file, &run.synth, &by_name, &call, run.binder, run.report,
        );
    }
    sort_report(run.report);
    std::mem::take(run.report)
}

/// Checks one class declaration, pushing into the run report.
///
/// Whole-declaration gates first (expression/abstract/declare/generic —
/// exactly one note, constructor excluded from the call set); then property
/// checks; then one class-level note per remaining family; then the
/// constructor joins the synthetic call set (or declines it via overloads).
fn check_one_class<'a>(decl: &'a ClassDecl, run: &mut ClassRun<'a, 'a>) {
    let span = binder_span_for(
        run.binder,
        run.file,
        decl.name.as_str(),
        decl.scope,
        decl.symbol,
        decl.span,
    );
    if let Some(reason) = whole_class_reason(decl) {
        run.report.unsupported.push(UnsupportedDecl {
            file: run.file,
            span,
            reason,
        });
        run.excluded.push(decl.name.as_str());
        return;
    }
    check_class_properties(decl, run);
    decline_class_families(decl, span, run);
    if decl.ctor_overloads {
        run.report.unsupported.push(UnsupportedDecl {
            file: run.file,
            span,
            reason: format!(
                "constructor overloads on class '{}': overload resolution is outside the subset",
                decl.name
            ),
        });
        run.excluded.push(decl.name.as_str());
        return;
    }
    run.synth.push(FunctionDecl {
        name: decl.name.clone(),
        span: decl.span,
        scope: decl.scope,
        symbol: decl.symbol,
        params: decl.ctor_params.clone(),
        params_complex: decl.ctor_complex,
        is_async: false,
        has_type_params: false,
        return_annotation: None,
        body: FunctionBody::Empty,
    });
}

/// Gates one class declaration for whole-declaration decline: `Some` carries
/// the single unsupported reason (expression, abstract, declare, and generic
/// forms check nothing — not even properties, whose `T` annotations would
/// otherwise mis-diagnose `TS2304`).
fn whole_class_reason(decl: &ClassDecl) -> Option<String> {
    if decl.form.is_expression {
        Some(format!(
            "class expression '{}': expressions are outside the subset",
            decl.name
        ))
    } else if decl.form.is_abstract {
        Some(format!(
            "abstract class '{}': abstract semantics are outside the subset",
            decl.name
        ))
    } else if decl.form.is_declare {
        Some(format!(
            "declare class '{}': ambient declarations are outside the subset",
            decl.name
        ))
    } else if decl.has_type_params {
        Some(format!(
            "generic class '{}': type parameters are outside the subset",
            decl.name
        ))
    } else {
        None
    }
}

/// Checks one class's properties through synthetic [`ConstDecl`]s.
///
/// Each property becomes one const-style declaration checked by [`check_one`]
/// with a disjoint occurrence node, so verdicts and messages match the const
/// subset by construction. The synthetic name is dotted (`Class.prop`): no
/// binder binding can ever carry a dot, so resolution always misses and the
/// diagnostic anchors at the property fact span (the oracle anchor) instead
/// of a same-named outer binding. Adapter-declined properties decline
/// per-property, quoting the adapter reason (the interface-member
/// precedent). Nodes reserve one counter step per property in order, so the
/// freshness table (built first) and the checks (built second) share nodes
/// without aliasing const/function space.
fn check_class_properties(decl: &ClassDecl, run: &mut ClassRun<'_, '_>) {
    let base = run.occurrence;
    let mut freshness = FreshnessTable::default();
    for (offset, prop) in decl.properties.iter().enumerate() {
        let node = class_occurrence_node(base, offset);
        if let Some(init) = prop.init_object.as_ref() {
            freshness.fresh.insert((run.file, node), init.fresh);
        }
    }
    for (offset, prop) in decl.properties.iter().enumerate() {
        let node = class_occurrence_node(base, offset);
        if let Some(reason) = prop.complex_reason.as_deref() {
            run.report.unsupported.push(UnsupportedDecl {
                file: run.file,
                span: prop.span,
                reason: format!("class '{}': property '{}': {reason}", decl.name, prop.name),
            });
            continue;
        }
        let synth = ConstDecl {
            name: format!("{}.{}", decl.name, prop.name),
            span: prop.span,
            scope: decl.scope,
            symbol: None,
            kind: DeclKind::Const,
            annotation: prop.annotation.clone(),
            init: prop.init,
            init_object: prop.init_object.clone(),
            init_array: None,
            cast: None,
        };
        let mut ctx = CheckCtx {
            file: run.file,
            node,
            db: &mut *run.db,
            freshness: &freshness,
            report: &mut *run.report,
            extra: &[],
        };
        // Class properties thread no alias tables (pinned P038 gap).
        check_one(&synth, run.binder, &mut ctx, &LocalAliasScope::EMPTY);
    }
    run.occurrence = base.saturating_add(offset_count(decl.properties.len()));
}

/// Saturating `usize` property count into the occurrence-counter step.
fn offset_count(len: usize) -> u32 {
    u32::try_from(len).unwrap_or(u32::MAX)
}

/// Pushes one class-level [`UnsupportedDecl`] per out-of-subset family
/// present on the declaration (see the module-level class rationale: one
/// note per family per class, never per method).
fn decline_class_families(decl: &ClassDecl, span: Span, run: &mut ClassRun<'_, '_>) {
    for family in &decl.declined {
        run.report.unsupported.push(UnsupportedDecl {
            file: run.file,
            span,
            reason: family.reason(decl.name.as_str()),
        });
    }
}

/// Occurrence [`NodeId`] for the `offset`-th synthetic class-property
/// declaration past `base`.
///
/// Property checks memoize through the same [`QueryDb`] as consts and
/// functions, so class indices land in a third disjoint high range
/// (saturating: skewed inputs pin the top, never wrap into other spaces).
#[must_use]
fn class_occurrence_node(base: u32, offset: usize) -> NodeId {
    const BASE: u32 = 0xC000_0000;
    NodeId(
        base.saturating_add(offset_count(offset))
            .saturating_add(BASE),
    )
}

/// Generic functions (P016, probed on tsc 7.0.2 `--strict --pretty false`).
///
/// [`check_generics`] checks identity-style `function id<T>(x: T): T`
/// declarations with explicit type arguments AND single-candidate inference
/// from argument literals, extended (P032) to single type parameters with
/// primitive `extends` constraints and primitive `=` defaults, and (P036)
/// to two or three independent single-primitive type parameters with
/// per-parameter inference from the corresponding argument positions. Each
/// (inferred or explicit) type argument binds in the scoped
/// [`InferenceTable`], substitutes for its parameter in the corresponding
/// value annotation, and checks through the same primitive comparisons (and
/// message shapes) as [`check_calls`]. A declared constraint bounds the
/// admitted kinds (violations diagnose `TS2345` on inference, `TS2344` on
/// explicit type arguments); a declared default fills missing inference
/// from non-literal arguments and missing trailing explicit type arguments.
/// Bodies check against the return name directly at declaration level,
/// exactly like tsc (call-independent).
///
/// Probe record (each `function id<T>(x: T): T { return x; }` unless noted):
///
/// - Explicit correct `id<number>(1)`: clean. Explicit wrong
///   `id<number>("oops")`: `TS2345: Argument of type 'string' is not
///   assignable to parameter of type 'number'.` at the argument (same shape
///   as non-generic calls).
/// - Explicit unknown `id<Nope>(1)`: `TS2304: Cannot find name 'Nope'.` at
///   the type-argument list (the solver anchors at the callee: no
///   type-argument spans exist in facts — documented fold).
/// - Explicit count `id<number, string>(1)`: `TS2558: Expected 1 type
///   arguments, but got 2.` (note the `type arguments` spelling; same
///   callee-span fold).
/// - Explicit union `id<number | string>(1)`: clean in tsc; the solver
///   declines (union type arguments are outside the subset — pinned
///   oracle-clean divergence).
/// - Inference binds from the argument, so an inferred call site itself
///   never errors: `const a: string = id(1)` reports `TS2322` AT THE USE,
///   never at the call (uses need expression facts — outside the subset).
///   The subset pins "inferred wrong" on the body-vs-`T` shape below while
///   the binding still records in the side table.
/// - No candidates: `id(u)` over `declare const u: number` binds `number`
///   from the identifier (clean); zero-parameter `mk<T>()` binds `unknown`
///   (clean). The subset has no expression facts, so non-literal arguments
///   decline with a reason (disclosed limit, never silent).
/// - Arity `id<number>()`: `TS2554` exactly like non-generic calls
///   (`Expected 1 arguments, but got 0.`).
/// - Bodies check against `T` directly: `return 1` reports `TS2322: Type
///   'number' is not assignable to type 'T'.` plus the elaboration `'T'
///   could be instantiated with an arbitrary type which could be unrelated
///   to 'number'.` (first line mirrored, elaboration folded like P015);
///   `return { v: 1 }` reports `Type '{ v: number; }' is not assignable to
///   type 'T'.` the same way. `return x` (the `T`-typed parameter) is clean
///   in tsc but inexpressible without expression facts, so non-literal
///   returns decline (P013's reason) while calls still check (P014
///   precedent: body checkability is irrelevant to call sites).
/// - Constrained and defaulted single parameters (P032, probed on tsc
///   7.0.2 `--strict --pretty false`; probes in
///   `.agent/scratch/p032-probes/`): `function idc<T extends string>(x:
///   T): T { return x; }` admits inferred `idc("s")` and explicit
///   `idc<string>("s")` silently; inferred `idc(1)` diagnoses `TS2345` at
///   the argument against the constraint (`Argument of type 'number' is not
///   assignable to parameter of type 'string'.`), while explicit
///   `idc<number>("s")` diagnoses `TS2344` (`Type 'number' does not satisfy
///   the constraint 'string'.`, anchored at the callee: no type-argument
///   spans exist in facts — the `TS2304`/`TS2558` fold). Satisfaction beats
///   argument checks (`idc<string>(1)` reports `TS2345`); name resolution
///   beats satisfaction (`idc<Nope>(1)` reports `TS2304`); `any`/`never`
///   satisfy every constraint while `unknown` diagnoses `TS2344`.
///   `function idd<T = number>(x: T): T { return x; }` admits inferred
///   `idd(1)` and explicit `idd<string>("s")` silently; the default fills
///   missing inference (`idd(u)` over an identifier is clean in tsc and
///   silent here), explicit overrides still check (`idd<string>(1)`
///   reports `TS2345`), and defaults never fill missing VALUE arguments
///   (`idd()` reports `TS2554`). Literal bodies check against `T` directly
///   with or without bounds (only the folded elaboration names the
///   constraint — the mirrored first line is unchanged), so the body path
///   is shared.
/// - Multi-parameter functions (P036, probed on tsc 7.0.2
///   `--strict --pretty false`; probes in `.agent/scratch/p036-probes/`):
///   `function pair<T, U>(x: T, y: U): T { return x; }` admits inferred
///   `pair(1, "s")` and explicit `pair<number, string>(1, "s")` silently;
///   per-position inference binds each parameter from its own argument, so
///   inference never errors at the call (identifier arguments decline per
///   position instead: `pair(u, v)` is clean in tsc, which binds from the
///   identifiers' types). Explicit mismatches diagnose per position with
///   first-mismatch priority: `pair<number, string>(true, "s")` reports
///   `TS2345` at the first argument, `pair<number, string>(1, true)` at the
///   second, and `pair<number, string>(true, 1)` only at the first.
///   Priority across phases mirrors tsc: explicit type-argument arity beats
///   value arity (`pair<number>(1)` reports `TS2558: Expected 2 type
///   arguments, but got 1.` — never `TS2554`; single-parameter
///   `id<number, string>()` reports `TS2558` the same way), value arity
///   beats argument checks but NOT name resolution (`pair<Nope, string>(1)` reports both
///   `TS2554` and `TS2304`; `pair<string, number>(1)` reports only
///   `TS2554`), name resolution beats satisfaction (each unknown name
///   reports its own `TS2304`: `pair<Nope, AlsoNope>(1, "s")` reports two),
///   and satisfaction beats argument checks (only the first `TS2344`
///   reports: `cpair<number, boolean>("s", true)` reports the `T`
///   violation alone). Constrained inference diagnoses per position
///   (`cpair(1, "s")` over `<T extends string, U>` reports `TS2345`
///   `number`-vs-`string` at the first argument; `<T, U extends number>`
///   with `("s", true)` at the second). Defaults compose per parameter:
///   `mix<string>("s", 1)` over `<T, U = number>` fills `U` from its
///   default silently, partial explicit lists are admitted
///   (`mix<string>(1, "s")` checks `1` against `string`), and the `TS2558`
///   spells the admitted range (`Expected 1-2 type arguments, but got 3.`);
///   a required parameter after an optional one declines (tsc `TS2706`).
///   Triple parameters check the same way (`tri(1, "s", true)` clean);
///   more than three decline. Four-plus value/type count mismatches and
///   non-bare annotations decline per position; the return annotation may
///   name any declared parameter (`: U` checks like `: T`). Empty angle
///   brackets decline (tsc `TS1099`, a grammar error).
/// - Declines, all probed: non-primitive bounds (`extends keyof T`,
///   `extends string | number`, object defaults), `in`/`out`/`const`
///   modifiers, and `keyof`/`infer`/conditional/mapped `T` positions — each
///   with a distinct reason. Union parameter `x: T | string` and object
///   return `: { v: T }` error in tsc ITSELF (the `return x` fails:
///   `Type 'string | T' is not assignable to type 'T'.`,
///   `Type 'T' is not assignable to type '{ v: T; }'.`) — solver declines
///   with reasons (pinned oracle-error divergences), as do the P032
///   `keyof` (`Type 'keyof T' is not assignable to type 'T'.`), conditional
///   (`Type 'number' is not assignable to type 'T extends string ? string :
///   number'.`), and mapped (`TS2353` on the returned literal) positions.
/// - Duplicate bare names (`f(1, "s")` over `(x: T, y: T)`) admit with
///   per-position checking (each literal verifies against its own binding,
///   so both stay silent): tsc instead binds the literal type `1`, then
///   reports `TS2345` on `"s"` — literal-type inference is outside the
///   subset (pinned oracle-error divergence).
///
/// Corollaries a generic declaration is never decl-silent: literal bodies
/// always diagnose (no literal inhabits bare `T`), non-literal bodies
/// decline, and every other shape declines. Calls verify independently.
///
/// Design law (H-002): inferred bindings are per-occurrence, per-parameter
/// side state in [`InferenceTable`], keyed by `(file, node, parameter)` —
/// never in [`TypeData`](pith_types::TypeData). Instantiation resolves to shared
/// builtin [`TypeId`]s through [`annotation_type`] (the shared interner's
/// canonical ids), so no parallel universe is interned and nothing here
/// needs the [`QueryDb`] memo (there is no new structure to memoize).
///
/// Code for explicit type-argument count mismatches (oracle `TS2558`).
pub const CODE_TYPE_ARITY: &str = "PITH2558";
/// Code for explicit type arguments violating a primitive constraint
/// (oracle `TS2344`).
pub const CODE_CONSTRAINT: &str = "PITH2344";

/// One generic `function id<T>(x: T): T` declaration: the plain
/// [`FunctionDecl`] plus its declared type-parameter facts verbatim from the
/// adapter.
///
/// Since P036 several independent type parameters admit (at most three):
/// [`GenericDecl::bounds`] rides one [`TypeParamBound`] per declared name,
/// and each value parameter checks against the bare name it cites, so
/// per-parameter inference, constraints, and defaults compose through the
/// P032 machinery without ever entering shared
/// [`TypeData`](pith_types::TypeData) (H-002).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericDecl {
    /// The underlying declaration (name/span/scope/symbol/params/return/body).
    pub decl: FunctionDecl,
    /// Declared type-parameter names in source order (`["T"]` for `id<T>`,
    /// `["T", "U"]` for `pair<T, U>`).
    pub type_params: Vec<String>,
    /// `true` when any parameter carries an `in`/`out`/`const` modifier
    /// (from the adapter's complexity flag).
    pub type_params_complex: bool,
    /// Bound texts parallel to [`GenericDecl::type_params`] (the adapter's
    /// per-parameter facts, driver-mapped verbatim). A missing entry reads
    /// as unconstrained with no default.
    pub bounds: Vec<TypeParamBound>,
}

/// One declared type parameter's bound texts: its verbatim constraint and
/// default (`Some("string")` for `<T extends string>`, `Some("number")`
/// for `<T = number>`); each `None` when absent. Only primitives admit;
/// the solver classifies each through the P032 machinery.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeParamBound {
    /// Verbatim constraint text; `None` when unconstrained.
    pub constraint: Option<String>,
    /// Verbatim default text; `None` when absent.
    pub default: Option<String>,
}

/// One call site that may instantiate a generic declaration.
///
/// Explicit type arguments ride a hand-fed seam: the adapter emits no
/// call-type-argument facts, so the driver supplies the written texts
/// (`Some(vec!["number"])` for `id<number>(1)`, `None` for `id(1)`).
/// Callee names, spans, arity, and inferred kinds still come from facts;
/// only the angle-bracket texts are hand-fed (disclosed, mirroring the
/// const-driver seam — the same seam M1's `compute` closures used).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericCall {
    /// The call-site facts (callee, spans, argument kinds).
    pub call: CallSite,
    /// Written type-argument texts in source order; `None` means inferred.
    pub explicit_args: Option<Vec<String>>,
}

/// Per-call-site inference side table (H-002 refined mode).
///
/// Maps each generic call occurrence to the [`TypeId`] each of its type
/// parameters bound — inferred from the corresponding literal argument, or
/// resolved from the explicit type argument (missing trailing positions
/// fill from their defaults). Instantiated structure is shared and
/// canonical (builtins through [`annotation_type`]); THIS table holds only
/// the occurrence-varying bindings, keyed by `(file, node, parameter)`.
#[derive(Clone, Debug, Default)]
struct InferenceTable {
    bindings: HashMap<(FileId, NodeId, u32), TypeId>,
}

impl InferenceTable {
    /// The recorded binding for one call occurrence's `index`-th type
    /// parameter, if any.
    #[must_use]
    fn binding(&self, file: FileId, node: NodeId, index: u32) -> Option<TypeId> {
        self.bindings.get(&(file, node, index)).copied()
    }

    /// Records one per-parameter binding and reads it back: verdicts
    /// substitute the RECORDED binding, never the transient local (H-002),
    /// even though the two agree here.
    fn record(&mut self, file: FileId, node: NodeId, index: usize, bound: TypeId) -> TypeId {
        let slot = u32::try_from(index).unwrap_or(u32::MAX);
        self.bindings.insert((file, node, slot), bound);
        self.binding(file, node, slot).unwrap_or(bound)
    }
}

/// One admitted primitive bound: canonical id plus display text.
///
/// Bounds admit through [`annotation_type`] plus [`boundary_annotation_type`]
/// (primitives and `any`/`unknown`/`never`); the structure is shared and
/// canonical, so per-occurrence bindings still live only in the
/// [`InferenceTable`] (H-002).
#[derive(Clone, Debug, PartialEq, Eq)]
struct GenericBound {
    /// Canonical builtin [`TypeId`] of the bound.
    id: TypeId,
    /// Canonical display text (`"string"`, `"number"`, ...).
    text: String,
}

/// What a checkable generic declaration carries into call checking: one
/// admitted bound per type parameter (body verdicts emit at declaration
/// level, so calls only need these for gating).
#[derive(Clone, Debug, PartialEq, Eq)]
struct GenericParamShape {
    /// Declared type-parameter name (`T`).
    name: String,
    /// Admitted `extends` bound, if declared.
    constraint: Option<GenericBound>,
    /// Admitted `=` default, if declared (fills missing inference and
    /// missing trailing explicit type arguments).
    default: Option<GenericBound>,
}

/// What a checkable generic declaration carries into call checking: the
/// admitted per-parameter bounds plus the value-to-type position map.
#[derive(Clone, Debug, PartialEq, Eq)]
struct GenericShape {
    /// Admitted bounds in type-parameter declaration order.
    params: Vec<GenericParamShape>,
    /// Value-parameter position to type-parameter index: value position
    /// `i` checks against `params[slots[i]]` (the bare name it cites).
    slots: Vec<usize>,
    /// The return annotation's bare type-parameter name (one of the
    /// declared names; bodies check against it directly).
    ret_name: String,
}

/// Checks every generic declaration in `decls` plus every instantiation in
/// `calls` for `file`, returning the sorted [`FileReport`].
///
/// Declaration phase (one note max per declaration, structural first):
/// type-parameter gates (complex, count, bound shapes, trailing defaults),
/// value-parameter gates (patterns, annotatedness, optionality, count, one
/// bare declared name per annotation), return gates (present, one bare
/// declared name), then the body check (literal returns diagnose against
/// the return name directly; non-literal returns and every other shape
/// decline). A generic declaration is never decl-silent (see the module
/// docs).
///
/// Call phase (priority mirrors tsc: explicit type-argument arity, then
/// value arity, then per-position name resolution, then per-position
/// constraint satisfaction, then per-position argument types): name
/// resolution mirrors [`check_calls`] (unresolved callees skip, overloads
/// decline); calls to declined declarations skip silently (the declaration
/// note covers them). Explicit type-argument counts below the trailing
/// defaults fill from those defaults; a value-arity miss still runs name
/// resolution (probed tsc 7.0.2 pairs `TS2554` with `TS2304`) but skips
/// satisfaction and argument checks; non-literal arguments under inference
/// bind the corresponding default when one is declared and decline
/// otherwise. All unknown names report, while satisfaction and argument
/// checks stop at the first mismatch; declines push exactly one
/// [`UnsupportedDecl`].
///
/// Spans mirror the oracle: body diagnostics at the declaration span,
/// too-few arity and `PITH2558`/`PITH2304` at the callee identifier,
/// too-many arity and `PITH2345` at the argument. Explicit-argument anchors
/// fold to the callee (no type-argument spans exist in facts).
#[must_use]
pub fn check_generics(
    file: FileId,
    decls: &[GenericDecl],
    calls: &[GenericCall],
    binder: &Binder,
) -> FileReport {
    let mut report = FileReport::default();
    let mut shapes: Vec<Option<GenericShape>> = Vec::with_capacity(decls.len());
    for generic in decls {
        shapes.push(check_generic_decl(file, generic, binder, &mut report));
    }
    let mut by_name: HashMap<&str, Vec<usize>> = HashMap::new();
    for (index, generic) in decls.iter().enumerate() {
        by_name
            .entry(generic.decl.name.as_str())
            .or_default()
            .push(index);
    }
    let mut ctx = GenericCallCtx {
        file,
        binder,
        shapes: &shapes,
        by_name: &by_name,
        inference: InferenceTable::default(),
        report: &mut report,
    };
    for (index, call_site) in calls.iter().enumerate() {
        check_one_generic_call(generic_occurrence_node(index), call_site, &mut ctx);
    }
    sort_report(&mut report);
    report
}

/// Mutable call-checking state for one [`check_generics`] run, bundled so
/// the per-call helper stays lean.
struct GenericCallCtx<'a, 'b> {
    file: FileId,
    binder: &'a Binder,
    shapes: &'a [Option<GenericShape>],
    by_name: &'a HashMap<&'b str, Vec<usize>>,
    inference: InferenceTable,
    report: &'a mut FileReport,
}

/// Pushes one [`UnsupportedDecl`] and returns `None`: the decline shorthand
/// for generic gates (every decline site returns `Option<..>`, so one
/// helper keeps them flat instead of repeating the push).
fn decline_to_none<T>(
    report: &mut FileReport,
    file: FileId,
    span: Span,
    reason: String,
) -> Option<T> {
    report
        .unsupported
        .push(UnsupportedDecl { file, span, reason });
    None
}

/// Gates one generic declaration and emits its body verdict.
///
/// Returns the [`GenericShape`] for call checking, or `None` after pushing
/// exactly one note. The SHAPE gates calls; the BODY never does: body
/// verdicts (literal diagnoses, non-literal and every other decline) emit
/// their note and the shape still returns, so calls check independently of
/// body checkability (P014 precedent).
fn check_generic_decl(
    file: FileId,
    generic: &GenericDecl,
    binder: &Binder,
    report: &mut FileReport,
) -> Option<GenericShape> {
    let decl = &generic.decl;
    let span = binder_span_for(
        binder,
        file,
        decl.name.as_str(),
        decl.scope,
        decl.symbol,
        decl.span,
    );
    let shape = match generic_decl_shape(generic) {
        Ok(shape) => shape,
        Err(reason) => return decline_to_none(report, file, span, reason),
    };
    match &decl.body {
        FunctionBody::SingleReturn(body) => {
            let _ = check_generic_body(file, span, &decl.name, &shape, body, report);
        }
        FunctionBody::NoBody { declared: true } => {
            let _: Option<GenericShape> = decline_to_none(
                report,
                file,
                span,
                format!("declare function '{}' has no body to check", decl.name),
            );
        }
        FunctionBody::NoBody { declared: false } => {
            let _: Option<GenericShape> = decline_to_none(
                report,
                file,
                span,
                format!(
                    "overload signature for '{}' has no body to check",
                    decl.name
                ),
            );
        }
        FunctionBody::Empty => {
            let _: Option<GenericShape> = decline_to_none(
                report,
                file,
                span,
                format!("empty body on '{}': nothing to check against", decl.name),
            );
        }
        FunctionBody::Complex => {
            let _: Option<GenericShape> = decline_to_none(
                report,
                file,
                span,
                format!(
                    "complex body on '{}': control flow is outside the subset",
                    decl.name
                ),
            );
        }
        FunctionBody::SequenceReturns(_)
        | FunctionBody::GuardReturn(_)
        | FunctionBody::BranchReturns(_)
        | FunctionBody::StraightBody(_)
        | FunctionBody::TryCatch(_)
        | FunctionBody::TryUnsupported { .. }
        | FunctionBody::Switch(_)
        | FunctionBody::SwitchUnsupported { .. }
        | FunctionBody::CountedFor(_)
        | FunctionBody::LoopUnsupported { .. }
        | FunctionBody::GuardThrow(_)
        | FunctionBody::StraightThrow(_) => {
            // Joined and straight returns over a bare type parameter need
            // per-position instantiation the subset refuses: decline like
            // complex bodies.
            let _: Option<GenericShape> = decline_to_none(
                report,
                file,
                span,
                format!(
                    "complex body on '{}': control flow is outside the subset",
                    decl.name
                ),
            );
        }
    }
    Some(shape)
}

/// Gates one generic declaration's type parameters, value parameters, and
/// return annotation into a [`GenericShape`]; `Err` carries the reason.
///
/// Gate order is structural-first: type-parameter modifiers, count, bound
/// shapes, and trailing defaults, then value-parameter
/// patterns/annotatedness/optionality/count, then bare-name annotation
/// shapes, then the return annotation. The body checks separately in
/// [`check_generic_body`].
fn generic_decl_shape(generic: &GenericDecl) -> Result<GenericShape, String> {
    if generic.type_params_complex {
        return Err("type parameter modifier is outside the subset".to_owned());
    }
    if generic.type_params.is_empty() {
        return Err(format!(
            "no type parameters on '{}': not a generic declaration",
            generic.decl.name
        ));
    }
    if generic.type_params.len() > 3 {
        return Err(format!(
            "multiple type parameters '{}' are outside the subset",
            generic.type_params.join(", ")
        ));
    }
    if let Some((first, next)) = required_after_optional(generic) {
        return Err(format!(
            "required type parameter '{next}' may not follow optional \
             '{first}': outside the subset"
        ));
    }
    let params = classify_type_params(generic)?;
    let decl = &generic.decl;
    if decl.params_complex {
        return Err("non-identifier parameter pattern is outside the subset".to_owned());
    }
    if decl.params.len() != params.len() {
        return Err(format!(
            "generic function '{}' has {} parameters: {} in the subset",
            decl.name,
            decl.params.len(),
            params_in_subset(params.len()),
        ));
    }
    let mut slots = Vec::with_capacity(decl.params.len());
    for param in &decl.params {
        if !param.annotated {
            return Err(format!(
                "unannotated parameter '{}' is outside the subset",
                param.name
            ));
        }
        if param.optional {
            return Err(format!(
                "optional parameter '{}' takes a range of arities, outside the subset",
                param.name
            ));
        }
        if param.is_rest {
            return Err(format!(
                "rest parameter '{}' is variadic, outside the subset",
                param.name
            ));
        }
        slots.push(bare_t_slot(
            param.annotation.as_deref().map_or("", str::trim),
            generic,
            param.name.as_str(),
        )?);
    }
    let annotation = decl.return_annotation.as_deref().map_or("", str::trim);
    if decl.return_annotation.is_none() {
        return Err(format!(
            "no return annotation on '{}': inference is outside the subset",
            decl.name
        ));
    }
    bare_t_return(annotation, generic)?;
    Ok(GenericShape {
        params,
        slots,
        ret_name: annotation.to_owned(),
    })
}

/// Spells the admitted value-parameter count the way the declaration gate
/// does, keeping the established single-parameter wording.
fn params_in_subset(arity: usize) -> String {
    if arity == 1 {
        "exactly one is".to_owned()
    } else {
        format!("exactly {arity} are")
    }
}

/// Names the first required type parameter following an optional
/// (defaulted) one, if any: tsc spells `TS2706` there, so the subset
/// declines instead of instantiating a list explicit type arguments could
/// never fill positionally.
fn required_after_optional(generic: &GenericDecl) -> Option<(String, String)> {
    let mut optional: Option<&String> = None;
    for (index, name) in generic.type_params.iter().enumerate() {
        let defaulted = generic
            .bounds
            .get(index)
            .is_some_and(|bound| bound.default.is_some());
        if defaulted {
            if optional.is_none() {
                optional = Some(name);
            }
        } else if let Some(first) = optional {
            return Some((first.clone(), name.clone()));
        }
    }
    None
}

/// Classifies every declared type parameter's constraint and default into
/// admitted primitive bounds through the P032 machinery. A missing
/// [`TypeParamBound`] entry reads as unconstrained with no default.
fn classify_type_params(generic: &GenericDecl) -> Result<Vec<GenericParamShape>, String> {
    let mut params = Vec::with_capacity(generic.type_params.len());
    for (index, name) in generic.type_params.iter().enumerate() {
        let bound = generic.bounds.get(index);
        let constraint = match bound.and_then(|entry| entry.constraint.as_deref()) {
            None => None,
            Some(text) => Some(classify_bound(text, "constraint")?),
        };
        let default = match bound.and_then(|entry| entry.default.as_deref()) {
            None => None,
            Some(text) => Some(classify_bound(text, "default")?),
        };
        params.push(GenericParamShape {
            name: name.clone(),
            constraint,
            default,
        });
    }
    Ok(params)
}

/// Canonical display text for one classified bound id.
///
/// Callers only pass ids that [`annotation_type`] or
/// [`boundary_annotation_type`] produced, so every arm is reachable on real
/// paths and the fallback never fires.
fn bound_display(id: TypeId) -> &'static str {
    if id == TypeStore::NUMBER {
        "number"
    } else if id == TypeStore::STRING {
        "string"
    } else if id == TypeStore::BOOLEAN {
        "boolean"
    } else if id == TypeStore::NULL {
        "null"
    } else if id == TypeStore::UNDEFINED {
        "undefined"
    } else if id == TypeStore::VOID {
        "void"
    } else if id == TypeStore::ANY {
        "any"
    } else if id == TypeStore::UNKNOWN {
        "unknown"
    } else if id == TypeStore::NEVER {
        "never"
    } else {
        "unknown"
    }
}

/// Decline reason for one non-primitive generic-position text, if complex.
///
/// Union, mapped, object, `keyof`, `infer`, and conditional shapes each name
/// themselves (in that order — a conditional holding `infer` reports
/// `infer`, a mapped type reports `mapped` rather than `object`); `None`
/// means the text is none of those (indexed `T[]`, concrete names, ...),
/// and the caller falls through to its own wording. `what` names the
/// position (`"parameter type"`, `"return type"`, `"constraint"`,
/// `"default"`).
fn complex_shape_reason(text: &str, what: &str) -> Option<String> {
    if text.contains('|') {
        Some(format!("union {what} '{text}' is outside the subset"))
    } else if text.starts_with('{') && text.contains('[') && text.contains(" in ") {
        Some(format!("mapped {what} '{text}' is outside the subset"))
    } else if text.starts_with('{') {
        Some(format!("object {what} '{text}' is outside the subset"))
    } else if text.contains("keyof") {
        Some(format!("keyof {what} '{text}' is outside the subset"))
    } else if text.contains("infer") {
        Some(format!("infer {what} '{text}' is outside the subset"))
    } else if text.contains('?') {
        Some(format!("conditional {what} '{text}' is outside the subset"))
    } else {
        None
    }
}

/// Classifies one constraint/default text into a primitive bound.
///
/// Primitives (plus `any`/`unknown`/`never`) admit through the shared maps;
/// every other shape declines via [`complex_shape_reason`], or the plain
/// outside-the-subset wording when it is none of those. `kind` names the
/// bound (`"constraint"` or `"default"`).
fn classify_bound(text: &str, kind: &str) -> Result<GenericBound, String> {
    let trimmed = text.trim();
    let id = annotation_type(trimmed).or_else(|| boundary_annotation_type(trimmed));
    if let Some(id) = id {
        return Ok(GenericBound {
            id,
            text: bound_display(id).to_owned(),
        });
    }
    if let Some(reason) = complex_shape_reason(trimmed, kind) {
        return Err(reason);
    }
    Err(format!("{kind} '{trimmed}' is outside the subset"))
}

/// Whether one explicit type argument satisfies a primitive constraint.
///
/// Same-primitive admits; `any`/`never` satisfy every constraint, and every
/// argument satisfies an `any`/`unknown` constraint (probed tsc 7.0.2:
/// `idc<any>` is clean, `idc<never>` reaches the argument check,
/// `idc<unknown>` diagnoses `TS2344`).
fn bound_satisfied(argument: TypeId, constraint: TypeId) -> bool {
    argument == constraint
        || argument == TypeStore::ANY
        || argument == TypeStore::NEVER
        || constraint == TypeStore::ANY
        || constraint == TypeStore::UNKNOWN
}

/// Resolves a value-parameter annotation to its type-parameter slot: the
/// annotation must name one declared parameter bare (`T`); duplicate names
/// across positions share one slot (each position still checks in order).
/// Union/mapped/object/`keyof`/`infer`/conditional shapes decline with
/// distinct reasons via [`complex_shape_reason`].
fn bare_t_slot(text: &str, generic: &GenericDecl, param: &str) -> Result<usize, String> {
    if let Some(slot) = generic.type_params.iter().position(|name| name == text) {
        return Ok(slot);
    }
    if let Some(reason) = complex_shape_reason(text, "parameter type") {
        return Err(reason);
    }
    if generic.type_params.len() == 1 {
        return Err(format!(
            "parameter type '{text}' for '{param}' is not the bare type parameter \
             '{}': outside the subset",
            generic.type_params[0],
        ));
    }
    Err(format!(
        "parameter type '{text}' for '{param}' is not one of the type parameters \
         '{}': outside the subset",
        generic.type_params.join(", "),
    ))
}

/// Requires the return annotation to name one declared type parameter bare
/// (`T`); union/mapped/object/`keyof`/`infer`/conditional shapes decline
/// with distinct reasons via [`complex_shape_reason`].
fn bare_t_return(text: &str, generic: &GenericDecl) -> Result<(), String> {
    if generic.type_params.iter().any(|name| name == text) {
        return Ok(());
    }
    if let Some(reason) = complex_shape_reason(text, "return type") {
        return Err(reason);
    }
    if generic.type_params.len() == 1 {
        return Err(format!(
            "return type '{text}' is not the bare type parameter '{}': outside the subset",
            generic.type_params[0],
        ));
    }
    Err(format!(
        "return type '{text}' is not one of the type parameters '{}': outside the subset",
        generic.type_params.join(", "),
    ))
}

/// Emits one generic declaration's body verdict, returning its
/// [`GenericShape`] for call checking.
///
/// Literal bodies always diagnose against the return name (no literal
/// inhabits a bare type parameter — probed tsc 7.0.2); non-literal returns
/// decline (the `T`-typed pass-through is clean in tsc but inexpressible
/// without expression facts). Returns `Some` in both cases: calls check
/// independently of body checkability (P014 precedent).
#[must_use]
fn check_generic_body(
    file: FileId,
    span: Span,
    name: &str,
    shape: &GenericShape,
    body: &FunctionReturn,
    report: &mut FileReport,
) -> Option<GenericShape> {
    let t_name = shape.ret_name.as_str();
    if let Some(init_object) = body.init_object.as_ref() {
        return check_generic_object_body(file, span, t_name, init_object, shape, report);
    }
    let Some(kind) = body.kind else {
        return decline_to_none(
            report,
            file,
            span,
            "missing return expression: nothing to check against".to_owned(),
        );
    };
    if kind == InitKind::NonLiteral {
        return decline_to_none(
            report,
            file,
            span,
            format!("non-literal return in '{name}' is outside the subset"),
        );
    }
    report.diagnostics.push(PithDiagnostic {
        code: CODE_MISMATCH.to_owned(),
        file,
        span,
        message: format!(
            "Type '{}' is not assignable to type '{t_name}'.",
            kind.name()
        ),
    });
    Some(shape.clone())
}

/// Emits one generic declaration's object-literal body verdict: the literal
/// spells in source order against `T` (probed tsc 7.0.2: `Type '{ v:
/// number; }' is not assignable to type 'T'.`). Non-literal and empty
/// members decline instead of forcing a spelling.
#[must_use]
fn check_generic_object_body(
    file: FileId,
    span: Span,
    t_name: &str,
    init_object: &ObjectInit,
    shape: &GenericShape,
    report: &mut FileReport,
) -> Option<GenericShape> {
    if init_object.members.is_empty() {
        return decline_to_none(
            report,
            file,
            span,
            "empty object return against a bare type parameter is outside the subset".to_owned(),
        );
    }
    let mut names: Vec<&str> = Vec::with_capacity(init_object.members.len());
    let mut types: Vec<&str> = Vec::with_capacity(init_object.members.len());
    for member in &init_object.members {
        if member.kind == ObjectMemberKind::NonLiteral {
            return decline_to_none(
                report,
                file,
                span,
                format!("non-literal member '{}' is outside the subset", member.name),
            );
        }
        names.push(member.name.as_str());
        types.push(member.kind.display_name());
    }
    report.diagnostics.push(PithDiagnostic {
        code: CODE_MISMATCH.to_owned(),
        file,
        span,
        message: format!(
            "Type '{}' is not assignable to type '{t_name}'.",
            object_type_text(&names, &types)
        ),
    });
    Some(shape.clone())
}

/// One admitted call's per-phase view: the occurrence node, the call-site
/// facts, and the admitted declaration shape, bundled so the per-phase
/// helpers stay lean.
struct GenericCallView<'a> {
    /// Occurrence node keying this call's [`InferenceTable`] bindings.
    node: NodeId,
    /// Callee name plus identifier span, whole-call span, argument facts.
    call: &'a CallSite,
    /// Admitted per-parameter bounds plus the value-to-type position map.
    shape: GenericShape,
}

/// Resolved per-parameter instantiation for one admitted call: canonical
/// ids plus display texts in type-parameter declaration order.
struct ResolvedCall {
    /// Canonical [`TypeId`] per type parameter.
    ids: Vec<TypeId>,
    /// Display text per type parameter.
    displays: Vec<String>,
}

/// Checks one generic instantiation, pushing into the context report.
///
/// Priority mirrors tsc (probed 7.0.2 P036): explicit type-argument arity
/// beats value arity, which beats per-position name resolution, which beats
/// per-position constraint satisfaction, which beats per-position argument
/// types. A value-arity miss still runs name resolution (the oracle pairs
/// `TS2554` with `TS2304`) but skips satisfaction and argument checks.
/// Calls to declined declarations skip silently (the declaration note
/// covers them).
fn check_one_generic_call(node: NodeId, call_site: &GenericCall, ctx: &mut GenericCallCtx<'_, '_>) {
    let call = &call_site.call;
    let file = ctx.file;
    let candidates = ctx.by_name.get(call.callee.as_str());
    let Some(candidates) = candidates else {
        if ctx
            .binder
            .unresolved()
            .iter()
            .any(|entry| entry.file == file && entry.name == call.callee)
        {
            return;
        }
        ctx.report.unsupported.push(UnsupportedDecl {
            file,
            span: call.callee_span,
            reason: format!(
                "call to undeclared name '{}': nothing to check against",
                call.callee
            ),
        });
        return;
    };
    if candidates.len() != 1 {
        ctx.report.unsupported.push(UnsupportedDecl {
            file,
            span: call.callee_span,
            reason: format!(
                "multiple declarations for '{}': overload resolution is outside the subset",
                call.callee
            ),
        });
        return;
    }
    let Some(shape) = ctx.shapes[candidates[0]].clone() else {
        // Declined at declaration level: the declaration note covers it.
        return;
    };
    let view = GenericCallView { node, call, shape };
    if let Some(texts) = call_site.explicit_args.as_ref() {
        if !check_type_arity(&view, texts, ctx) {
            return;
        }
        let arity_ok = check_value_arity(&view, ctx);
        let Some(resolved) = resolve_explicit(&view, texts, ctx) else {
            return;
        };
        if !arity_ok {
            return;
        }
        if !check_constraints(&view, &resolved, ctx) {
            return;
        }
        check_arg_types(&view, &resolved, ctx, false);
    } else {
        let arity_ok = check_value_arity(&view, ctx);
        if !arity_ok {
            return;
        }
        let Some(resolved) = resolve_inferred(&view, ctx) else {
            return;
        };
        check_arg_types(&view, &resolved, ctx, true);
    }
}

/// Gates one call's explicit type-argument count (probed tsc 7.0.2 P036):
/// trailing defaulted parameters may go missing and fill from their
/// defaults (`mix<string>` over `<T, U = number>`), anything else diagnoses
/// `PITH2558` at the callee (no type-argument spans exist in facts — the
/// `TS2304` fold), and an empty bracket list declines (tsc spells `TS1099`,
/// a grammar error). Returns false after pushing one diagnostic or note.
fn check_type_arity(
    view: &GenericCallView<'_>,
    texts: &[String],
    ctx: &mut GenericCallCtx<'_, '_>,
) -> bool {
    let file = ctx.file;
    if texts.is_empty() {
        ctx.report.unsupported.push(UnsupportedDecl {
            file,
            span: view.call.callee_span,
            reason: format!(
                "call to '{}': empty type argument list is outside the subset",
                view.call.callee
            ),
        });
        return false;
    }
    let total = view.shape.params.len();
    let defaulted = trailing_defaults(&view.shape);
    let min = total - defaulted;
    if texts.len() < min || texts.len() > total {
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_TYPE_ARITY.to_owned(),
            file,
            span: view.call.callee_span,
            message: format!(
                "Expected {} type arguments, but got {}.",
                type_arity_expected(total, min, defaulted),
                texts.len()
            ),
        });
        return false;
    }
    true
}

/// Spells the admitted explicit type-argument count the way tsc does: the
/// bare total without defaults (`Expected 2 type arguments`), or the
/// `MIN-N` range with trailing defaults (`Expected 1-2 type arguments` —
/// probed tsc 7.0.2 P036).
fn type_arity_expected(total: usize, min: usize, defaulted: usize) -> String {
    if defaulted == 0 {
        format!("{total}")
    } else {
        format!("{min}-{total}")
    }
}

/// Counts trailing defaulted type parameters: only those may go missing
/// from an explicit type-argument list (the declaration gate keeps
/// defaults trailing, mirroring tsc's `TS2706`).
fn trailing_defaults(shape: &GenericShape) -> usize {
    shape
        .params
        .iter()
        .rev()
        .take_while(|param| param.default.is_some())
        .count()
}

/// Gates one call's value arity: exactly one argument per type parameter.
/// Too-few anchors at the callee, too-many at the first excess argument
/// (the P014 law). Returns false after pushing `PITH2554`; the caller
/// still runs name resolution on a miss (probed tsc 7.0.2 P036).
fn check_value_arity(view: &GenericCallView<'_>, ctx: &mut GenericCallCtx<'_, '_>) -> bool {
    let want = view.shape.params.len();
    if view.call.args.len() == want {
        return true;
    }
    let span = if view.call.args.len() < want {
        view.call.callee_span
    } else {
        view.call.args[want].span
    };
    ctx.report.diagnostics.push(PithDiagnostic {
        code: CODE_ARITY.to_owned(),
        file: ctx.file,
        span,
        message: format!(
            "Expected {want} arguments, but got {}.",
            view.call.args.len()
        ),
    });
    false
}

/// Resolves every type parameter from an admitted explicit type-argument
/// list, recording each binding in the [`InferenceTable`].
///
/// Missing trailing positions fill from their defaults (the count gate
/// guarantees those exist — anything else declines rather than inventing);
/// union/object texts decline (tsc admits them but the subset cannot spell
/// checks against them — pinned oracle-clean divergence); every unknown
/// name diagnoses `PITH2304` (all report, never just the first — probed
/// tsc 7.0.2 P036). Returns `None` after a decline or when any name
/// missed (satisfaction and argument checks then skip).
#[must_use]
fn resolve_explicit(
    view: &GenericCallView<'_>,
    texts: &[String],
    ctx: &mut GenericCallCtx<'_, '_>,
) -> Option<ResolvedCall> {
    let file = ctx.file;
    let mut resolved = ResolvedCall {
        ids: Vec::with_capacity(view.shape.params.len()),
        displays: Vec::with_capacity(view.shape.params.len()),
    };
    let mut missed = false;
    for (index, param) in view.shape.params.iter().enumerate() {
        if let Some(written) = texts.get(index) {
            let text = written.trim();
            if text.contains('|') || text.starts_with('{') {
                ctx.report.unsupported.push(UnsupportedDecl {
                    file,
                    span: view.call.callee_span,
                    reason: format!(
                        "call to '{}': type argument '{text}' is outside the subset",
                        view.call.callee
                    ),
                });
                return None;
            }
            let Some(bound) = annotation_type(text) else {
                ctx.report.diagnostics.push(PithDiagnostic {
                    code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                    file,
                    span: view.call.callee_span,
                    message: format!("Cannot find name '{text}'."),
                });
                missed = true;
                resolved.ids.push(TypeStore::UNKNOWN);
                resolved.displays.push(text.to_owned());
                continue;
            };
            let bound = ctx.inference.record(file, view.node, index, bound);
            resolved.ids.push(bound);
            resolved.displays.push(text.to_owned());
        } else {
            let Some(default) = param.default.as_ref() else {
                ctx.report.unsupported.push(UnsupportedDecl {
                    file,
                    span: view.call.callee_span,
                    reason: format!(
                        "call to '{}': no type argument for '{}': expression facts are \
                         outside the subset",
                        view.call.callee, param.name,
                    ),
                });
                return None;
            };
            let bound = ctx.inference.record(file, view.node, index, default.id);
            resolved.ids.push(bound);
            resolved.displays.push(default.text.clone());
        }
    }
    if missed {
        return None;
    }
    Some(resolved)
}

/// Binds every type parameter from its corresponding literal argument,
/// recording each binding in the [`InferenceTable`].
///
/// Non-literal positions fill from their own default (the oracle binds
/// from the identifier's type — clean either way) and decline with no
/// candidate otherwise (first failure only). The caller guarantees
/// value-arity alignment, so every position has an argument. Returns
/// `None` after pushing the decline note.
#[must_use]
fn resolve_inferred(
    view: &GenericCallView<'_>,
    ctx: &mut GenericCallCtx<'_, '_>,
) -> Option<ResolvedCall> {
    let file = ctx.file;
    let mut bound: Vec<Option<(TypeId, String)>> = vec![None; view.shape.params.len()];
    for (position, argument) in view.call.args.iter().enumerate() {
        // Aligned by the caller's arity gate: one slot per value position.
        let slot = view.shape.slots[position];
        let param = &view.shape.params[slot];
        if argument.kind == InitKind::NonLiteral {
            if let Some(default) = param.default.as_ref() {
                let id = ctx.inference.record(file, view.node, slot, default.id);
                bound[slot] = Some((id, default.text.clone()));
                continue;
            }
            ctx.report.unsupported.push(UnsupportedDecl {
                file,
                span: argument.span,
                reason: format!(
                    "call to '{}': cannot infer '{}' from a non-literal argument: \
                     expression facts are outside the subset",
                    view.call.callee, param.name,
                ),
            });
            return None;
        }
        let kind = argument.kind.type_id();
        let id = ctx.inference.record(file, view.node, slot, kind);
        let display = primitive_name(id).unwrap_or("unknown").to_owned();
        bound[slot] = Some((id, display));
    }
    // Parameters no value position cites (duplicate bare names elsewhere)
    // bind `unknown`, exactly like tsc's empty inference.
    let mut resolved = ResolvedCall {
        ids: Vec::with_capacity(bound.len()),
        displays: Vec::with_capacity(bound.len()),
    };
    for slot in bound {
        if let Some((id, display)) = slot {
            resolved.ids.push(id);
            resolved.displays.push(display);
        } else {
            resolved.ids.push(TypeStore::UNKNOWN);
            resolved.displays.push("unknown".to_owned());
        }
    }
    Some(resolved)
}

/// Verifies every explicitly resolved type argument against its declared
/// constraint (probed tsc 7.0.2 P036): the first violation diagnoses
/// `PITH2344` at the callee (no type-argument spans exist in facts — the
/// `TS2304`/`TS2558` fold), beating argument checks. Returns false after
/// pushing it.
fn check_constraints(
    view: &GenericCallView<'_>,
    resolved: &ResolvedCall,
    ctx: &mut GenericCallCtx<'_, '_>,
) -> bool {
    for (index, param) in view.shape.params.iter().enumerate() {
        let Some(constraint) = param.constraint.as_ref() else {
            continue;
        };
        if !bound_satisfied(resolved.ids[index], constraint.id) {
            ctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_CONSTRAINT.to_owned(),
                file: ctx.file,
                span: view.call.callee_span,
                message: format!(
                    "Type '{}' does not satisfy the constraint '{}'.",
                    resolved.displays[index], constraint.text,
                ),
            });
            return false;
        }
    }
    true
}

/// Checks every value argument against its substituted parameter type
/// (probed tsc 7.0.2 P036): only the first mismatch reports `PITH2345` at
/// its argument. Non-literal arguments skip per-argument (P014 precedent).
/// Under inference each position verifies against its declared constraint
/// when one exists (violations spell `TS2345` with the constraint text,
/// never `TS2344`); unconstrained inferred positions skip (the slot was
/// just bound from that very literal, so the comparison is vacuous by
/// construction — duplicate bare names sharing one slot still verify per
/// position, never against a later overwrite). Under explicit arguments
/// each position checks against its resolved display.
fn check_arg_types(
    view: &GenericCallView<'_>,
    resolved: &ResolvedCall,
    ctx: &mut GenericCallCtx<'_, '_>,
    inferred: bool,
) {
    for (position, argument) in view.call.args.iter().enumerate() {
        if argument.kind == InitKind::NonLiteral {
            continue;
        }
        // Aligned by the caller's arity gate: one slot per value position.
        let slot = view.shape.slots[position];
        let (expected, display) = if inferred {
            let Some(constraint) = view.shape.params[slot].constraint.as_ref() else {
                continue;
            };
            (constraint.id, constraint.text.as_str())
        } else {
            (resolved.ids[slot], resolved.displays[slot].as_str())
        };
        if argument.kind.type_id() != expected {
            ctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_ARG_TYPE.to_owned(),
                file: ctx.file,
                span: argument.span,
                message: format!(
                    "Argument of type '{}' is not assignable to parameter of type '{display}'.",
                    argument.kind.name(),
                ),
            });
            return;
        }
    }
}

/// Occurrence [`NodeId`] for the `index`-th generic call instantiation.
///
/// Generic inference bindings key per call occurrence; the range stays
/// disjoint from const nodes ([`occurrence_node`]) and function nodes
/// ([`function_occurrence_node`]) so all three checkers may share nothing
/// while never aliasing.
#[must_use]
fn generic_occurrence_node(index: usize) -> NodeId {
    const BASE: u32 = 0x8000_0000;
    NodeId(
        u32::try_from(index)
            .unwrap_or(u32::MAX)
            .saturating_add(BASE),
    )
}

/// Narrowing over union annotations (P015, probed on tsc 7.0.2
/// `--strict --pretty false`).
///
/// [`check_narrowing`] checks union-annotated `const`s (`number | string`
/// over primitives) and `unknown`-annotated `const`s plus
/// identifier-initializer *uses* of those consts (`const b: string = x;`)
/// against [`TypeofGuard`] regions. Other non-union declarations delegate to
/// [`check_one`] unchanged, so verdicts outside narrowing match by
/// construction.
///
/// Probe record (each `declare const x: <union>` unless noted):
///
/// - `if (typeof x === "string") { const a: number = x; }` diagnoses
///   `Type 'string' is not assignable to type 'number'.` (single line, no
///   elaboration); the matching `const b: string = x;` is silent.
/// - `!==` flips: the then branch refines to the complement, `else`
///   refines opposite (`else` of `=== "string"` is `number`, of `!==` is
///   `string`). Early-return `if (typeof x !== "string") return;` (also
///   `return <expr>;`, `throw`, single-statement blocks) refines the code
///   after; `===` early-return refines to the complement.
/// - Unguarded uses diagnose over the full union, first line
///   `Type 'string | number' is not assignable to type 'boolean'.` tsc adds
///   an elaboration line (`  Type 'string' is not assignable …`) whose
///   member choice is deterministic per union but varies across unions by no
///   rule this subset reproduces, so only the first line is mirrored
///   (documented differential fold; independently re-probed V015).
/// - Union display order is canonical, never source order:
///   `void | string | number | boolean | null | undefined` (full six-member
///   order independently re-probed V015; earlier pairs: `void` before
///   `number`; `string` before `number` before `boolean`;
///   `boolean, null, undefined` tail; `string` before `undefined`).
/// - Guard literals outside the union narrow to `never` (uses silent);
///   `==` narrows exactly like `===` but is declined (subset pins
///   `===`/`!==`); `||` conditions do not narrow (full-union diagnostic);
///   equality tests (`x === "hi"`) narrow but are declined.
/// - `const x: number | string = 1;` (literal init) does NOT narrow: a
///   `typeof x === "string"` branch stays silent in tsc, so literal-init
///   targets never enter the narrowing environment. `declare const` and
///   non-literal-init targets narrow normally.
/// - A use inside a nested closure sees the full union (no refinement
///   crosses function boundaries).
///
/// `unknown` targets (P033, probed on tsc 7.0.2 `--strict --pretty false`;
/// probes in `.agent/scratch/p033-probes/`):
///
/// - `declare const uv: unknown;` enters the environment exactly like a
///   union target, except EVERY initializer shape enters — literal inits
///   included (`const u: unknown = "s"` still refines through guards and
///   still diagnoses `Type 'unknown'` unguarded: no assignment narrowing is
///   observable). `unknown` also absorbs every union it joins
///   (`number | unknown` is `unknown` in tsc), so those declarations route
///   through unknown targets as well.
/// - Unguarded uses diagnose `Type 'unknown' is not assignable to type
///   'string'.` (also against `number`, and against `never`); guarded
///   `=== "string"` branches refine to the single matched primitive (match
///   silent, mismatch `Type 'string' is not assignable to type 'number'.`),
///   and complements fall back to `unknown` (the `else` of `=== "string"`
///   diagnoses `Type 'unknown' …`). Early-return refines identically.
/// - `unknown`- and `any`-expected uses are silent in every position (for
///   union targets too — both probed clean); `never`-expected uses diagnose
///   like any other `T` (unguarded unions spell the full union, probed).
/// - Non-primitive guard literals decline: `typeof uv === "object"` refines
///   to `object | null` in tsc and `"bigint"` to `bigint` — both
///   unspellable in-subset, so those regions decline with reasons (pinned
///   oracle-error divergences, never forced verdicts).
/// - Genuinely-unknown targets (no annotation, no literal init) never enter
///   and keep the legacy non-literal note; `any`-annotated declarations
///   stay on the [`check_one`] path (their uses are silent in tsc but
///   unlinkable in-subset — a pinned oracle-clean divergence).
///
/// Design law (H-002): narrowed verdicts are per-occurrence side state
/// (computed from the [`NarrowedUse`] occurrence span against guard spans at
/// check time), never interned variants. Unions have no [`TypeData`] shape —
/// the canonical spelling is display text only — so union declarations skip
/// the [`QueryDb`] memo (single/object shapes still memoize via [`check_one`]).
///
/// One identifier-initializer use of a union-annotated const.
///
/// `const b: string = x;` where `x` is a union const: `annotation` is the
/// expected text, `target` the referenced name, `init_span` the identifier
/// occurrence span (region tests run on it, never on the declaration span).
/// The driver feeds these from adapter decl facts whose initializer span
/// slices to a bare identifier (disclosed seam — the adapter emits no
/// expression facts); every other shape travels as [`ConstDecl`] and keeps
/// today's verdicts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NarrowedUse {
    /// Declared name of the use, resolved like [`ConstDecl::name`].
    pub name: String,
    /// Fallback span, used only when binder resolution misses.
    pub span: Span,
    /// Per-file scope index of the use declarator.
    pub scope: u32,
    /// Exact binder identity when the driver resolved it.
    pub symbol: Option<SymbolId>,
    /// Raw expected annotation text (`Some("number")` maps to one primitive;
    /// anything else declines).
    pub annotation: String,
    /// Referenced union const name as written in the initializer.
    pub target: String,
    /// Span of the initializer identifier (region-test anchor).
    pub init_span: Span,
}

/// One straight-line `typeof` guard: driver-mapped from the adapter's
/// `TypeofGuardFact` (mechanical field copy).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeofGuard {
    /// Target name as written in `typeof <target>`.
    pub target: String,
    /// Matched literal text (`"string"`).
    pub matched: String,
    /// `true` for `!==` (regions flip).
    pub negated: bool,
    /// Then-branch statement span.
    pub then_span: Span,
    /// Plain-`else` statement span, if any.
    pub else_span: Option<Span>,
    /// Early-exit shape: the code at/after [`TypeofGuard::if_span`] refines.
    pub early_return: bool,
    /// Whole `if` statement span.
    pub if_span: Span,
}

/// One span narrowing refuses to reason inside: driver-mapped from the
/// adapter's `DeclineRegionFact` (mechanical field copy).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclineRegion {
    /// Whole-statement span (guard or nested function).
    pub span: Span,
    /// Why narrowing declines here (surfaces in the [`UnsupportedDecl`]).
    pub reason: String,
}

/// Canonical union display order, mirroring tsc 7.0.2 (see the narrowing
/// probe record above).
const UNION_ORDER: [&str; 6] = ["void", "string", "number", "boolean", "null", "undefined"];

/// Canonical position of one union member name, or `None` outside the subset.
#[must_use]
fn union_order(name: &str) -> Option<usize> {
    UNION_ORDER.iter().position(|member| *member == name)
}

/// Display name of one interned primitive [`TypeId`], or `None` for
/// non-primitive ids (callers only pass member ids, so `None` is unreachable
/// on real paths).
#[must_use]
fn primitive_name(id: TypeId) -> Option<&'static str> {
    if id == TypeStore::NUMBER {
        Some("number")
    } else if id == TypeStore::STRING {
        Some("string")
    } else if id == TypeStore::BOOLEAN {
        Some("boolean")
    } else if id == TypeStore::VOID {
        Some("void")
    } else if id == TypeStore::UNDEFINED {
        Some("undefined")
    } else if id == TypeStore::NULL {
        Some("null")
    } else {
        None
    }
}

/// Parses `number | string` into canonical-order `(display-name, TypeId)`
/// members. Returns `None` for non-primitive members, empty pieces, and
/// degenerate (< 2 distinct members) unions — callers decline, never verdict.
#[must_use]
fn parse_union_annotation(text: &str) -> Option<Vec<(&'static str, TypeId)>> {
    let mut members: Vec<(usize, &'static str, TypeId)> = Vec::new();
    for piece in text.split('|') {
        let piece = piece.trim();
        let order = union_order(piece)?;
        // `union_order` accepts exactly the `annotation_type` set, so this
        // `?` is unreachable on real paths (kept fallible, never panicking).
        let id = annotation_type(piece)?;
        if members.iter().all(|(_, name, _)| *name != piece) {
            members.push((order, UNION_ORDER[order], id));
        }
    }
    if members.len() < 2 {
        return None;
    }
    members.sort_by_key(|(order, _, _)| *order);
    Some(
        members
            .into_iter()
            .map(|(_, name, id)| (name, id))
            .collect(),
    )
}

/// Spells a union the way tsc elaborations do: `string | number`.
#[must_use]
fn union_spelling(members: &[(&'static str, TypeId)]) -> String {
    members
        .iter()
        .map(|(name, _)| *name)
        .collect::<Vec<&str>>()
        .join(" | ")
}

/// One union-annotated declaration available as a narrowing target.
#[derive(Debug)]
struct UnionTarget {
    /// Declared name (linkage is by name; shadowing declines, see below).
    name: String,
    /// Canonical-order members.
    members: Vec<(&'static str, TypeId)>,
    /// Cached [`union_spelling`].
    spelling: String,
    /// Literal-initialized targets never narrow (probed tsc 7.0.2).
    has_literal_init: bool,
}

/// One `unknown`-annotated declaration available as a narrowing target.
///
/// Unlike [`UnionTarget`], there are no members to spell: unguarded and
/// complement uses diagnose `Type 'unknown' …`, while matched guard sides
/// refine to the single matched primitive. Every initializer shape enters
/// (probed tsc 7.0.2 P033: literal-init `unknown` still refines and still
/// diagnoses unguarded — no assignment narrowing is observable).
#[derive(Debug)]
struct UnknownTarget {
    /// Declared name (linkage is by name; shadowing declines, like unions).
    name: String,
}

/// One narrowing target: a union-annotated const or an `unknown`-annotated
/// one. Both live in the same per-occurrence environment (H-002: side state
/// keyed by declaration, never interned [`TypeData`] variants).
#[derive(Debug)]
enum NarrowTarget {
    /// A union-annotated const with canonical members.
    Union(UnionTarget),
    /// An `unknown`-annotated const (memberless: spells `unknown`).
    Unknown(UnknownTarget),
}

impl NarrowTarget {
    /// The declared name (linkage is by name for both variants).
    #[must_use]
    fn name(&self) -> &str {
        match self {
            Self::Union(target) => target.name.as_str(),
            Self::Unknown(target) => target.name.as_str(),
        }
    }
}

/// Whether `inner` lies fully inside `outer` (same file, closed bounds).
fn span_contains(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.lo <= inner.lo && inner.hi <= outer.hi
}

/// Checks union-annotated declarations plus identifier-uses for `file`,
/// returning the sorted [`FileReport`].
///
/// Declaration routing: object annotations delegate to [`check_one`];
/// `unknown` annotations (and unions holding an `unknown` member, which tsc
/// absorbs into `unknown`) enter unknown targets — every initializer shape,
/// since literal-init `unknown` still refines (probed tsc 7.0.2 P033);
/// plain unions parse to canonical members (unknown names diagnose
/// `PITH2304` like object members, shapes/degenerates decline); only
/// missing-init and non-literal-init union targets enter the narrowing
/// environment (literal-init targets check against the union but never
/// narrow — probed tsc 7.0.2). Other non-union declarations delegate to
/// [`check_one`] unchanged.
///
/// Use routing, in order: expected-type gating (`any`/`unknown` expectations
/// are clean before linkage — probed silent in every position; `never` and
/// single primitives check; object/union expectations decline exactly like
/// before; unknown names diagnose `PITH2304`), target linkage (missing
/// targets keep the legacy non-literal note; shadowed or closure-ambiguous
/// targets decline), literal-init union targets decline, decline regions
/// decline, then guard refinement (all applicable guards must agree on one
/// primitive; complements that are not single primitives decline;
/// guard literals outside the union decline positive branches and fall back
/// to the full union on complements). Unguarded union uses diagnose over
/// the full union spelling; unguarded unknown uses diagnose `unknown`.
#[must_use]
pub fn check_narrowing(
    file: FileId,
    decls: &[ConstDecl],
    facts: &NarrowingFacts<'_>,
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    let mut freshness = FreshnessTable::default();
    for (index, decl) in decls.iter().enumerate() {
        if let Some(init) = decl.init_object.as_ref() {
            freshness
                .fresh
                .insert((file, occurrence_node(index)), init.fresh);
        }
    }
    let mut name_counts: HashMap<&str, usize> = HashMap::new();
    for decl in decls {
        *name_counts.entry(decl.name.as_str()).or_default() += 1;
    }
    let mut env: Vec<NarrowTarget> = Vec::new();
    let mut report = FileReport::default();
    for (index, decl) in decls.iter().enumerate() {
        let mut ctx = NarrowDeclCtx {
            binder,
            db: &mut *db,
            freshness: &freshness,
            env: &mut env,
            report: &mut report,
        };
        check_narrowing_decl(file, occurrence_node(index), decl, &mut ctx);
    }
    // `name_counts` borrows `decls`, which outlives this body, so the
    // use-phase context can hold it by reference.
    let mut ctx = NarrowUseCtx {
        guards: facts.guards,
        declines: facts.declines,
        env: &env,
        name_counts: &name_counts,
        binder,
        report: &mut report,
    };
    for use_ in facts.uses {
        check_narrowing_use(file, use_, &mut ctx);
    }
    sort_report(&mut report);
    report
}

/// Checks one declaration for [`check_narrowing`]: union routing plus
/// environment registration (see the function docs).
/// Splits a union annotation into unknown plain names versus shaped pieces.
///
/// Unknown alphanumeric names diagnose (`TS2304`); shaped pieces (unions
/// within unions, objects, anything non-identifier) decline. Known
/// primitives pass through silently in neither list.
fn split_union_members(annotation: &str) -> (Vec<&str>, bool) {
    let mut unknown: Vec<&str> = Vec::new();
    let mut shaped = false;
    for piece in annotation.split('|').map(str::trim) {
        if annotation_type(piece).is_none() {
            if !piece.is_empty()
                && piece
                    .chars()
                    .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
            {
                unknown.push(piece);
            } else {
                shaped = true;
            }
        }
    }
    (unknown, shaped)
}

/// Routes a union-annotated declaration for [`check_narrowing_decl`]:
/// unknown names diagnose (`TS2304`), shaped members decline, degenerates
/// decline, object initializers decline, otherwise the initializer checks
/// against the canonical members.
fn check_narrowing_union(
    file: FileId,
    span: Span,
    decl: &ConstDecl,
    annotation: &str,
    nctx: &mut NarrowDeclCtx<'_>,
) {
    let (unknown, shaped) = split_union_members(annotation);
    if !unknown.is_empty() {
        for name in unknown {
            nctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                file,
                span,
                message: format!("Cannot find name '{name}'."),
            });
        }
        return;
    }
    if shaped {
        nctx.report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("union member shape in '{annotation}' is outside the subset"),
        });
        return;
    }
    let Some(members) = parse_union_annotation(annotation) else {
        nctx.report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("degenerate union annotation '{annotation}' is outside the subset"),
        });
        return;
    };
    let spelling = union_spelling(&members);
    if decl.init_object.is_some() {
        nctx.report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!(
                "object initializer against union annotation '{annotation}' is outside the subset"
            ),
        });
        return;
    }
    check_union_init(file, span, decl, members, spelling, nctx);
}

fn check_narrowing_decl(
    file: FileId,
    node: NodeId,
    decl: &ConstDecl,
    nctx: &mut NarrowDeclCtx<'_>,
) {
    let binder = nctx.binder;
    let db: &mut QueryDb = &mut *nctx.db;
    let freshness = nctx.freshness;
    let report: &mut FileReport = &mut *nctx.report;
    let span = binder_span(binder, file, decl);
    let Some(raw) = decl.annotation.as_deref() else {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "no annotation: inference is outside the subset".to_owned(),
        });
        return;
    };
    let annotation = raw.trim();
    if decl.init.is_some() && decl.init_object.is_some() {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "contradictory initializer facts: primitive kind with object members"
                .to_owned(),
        });
        return;
    }
    if decl.init_array.is_some() && (decl.init.is_some() || decl.init_object.is_some()) {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "contradictory initializer facts: array members with \
                another initializer shape"
                .to_owned(),
        });
        return;
    }
    if annotation.starts_with('{') {
        let mut ctx = CheckCtx {
            file,
            node,
            db,
            freshness,
            report,
            extra: &[],
        };
        // Array initializers need the array-aware object path in
        // [`check_one`]; every other shape keeps the direct object path.
        // Both thread no alias tables (pinned P038 gap: narrowing keeps
        // today's verdicts for alias annotations).
        if decl.init_array.is_some() {
            check_one(decl, binder, &mut ctx, &LocalAliasScope::EMPTY);
        } else {
            check_object(decl, span, annotation, decl.init, &mut ctx);
        }
        return;
    }
    // `unknown` absorbs every union it joins (tsc: `number | unknown` is
    // `unknown`, probed P033), so plain `unknown` and unions holding an
    // `unknown` member both route through unknown targets. `any`/`never`
    // members keep today's verdicts below (pre-existing, outside this task).
    if annotation.split('|').any(|piece| piece.trim() == "unknown") {
        check_unknown_init(file, span, decl, nctx);
        return;
    }
    if !annotation.contains('|') {
        let mut ctx = CheckCtx {
            file,
            node,
            db: &mut *db,
            freshness,
            report: &mut *report,
            extra: &[],
        };
        check_one(decl, binder, &mut ctx, &LocalAliasScope::EMPTY);
        return;
    }
    check_narrowing_union(file, span, decl, annotation, nctx);
}

/// Checks a union-annotated declaration's initializer: missing and
/// non-literal initializers decline with a note and enter the narrowing
/// environment; other literals diagnose when foreign to the canonical
/// members.
fn check_union_init(
    file: FileId,
    span: Span,
    decl: &ConstDecl,
    members: Vec<(&'static str, TypeId)>,
    spelling: String,
    nctx: &mut NarrowDeclCtx<'_>,
) {
    match decl.init {
        None => {
            nctx.report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: "missing initializer: nothing to check against".to_owned(),
            });
            nctx.env.push(NarrowTarget::Union(UnionTarget {
                name: decl.name.clone(),
                members,
                spelling,
                has_literal_init: false,
            }));
        }
        Some(InitKind::NonLiteral) => {
            nctx.report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: "non-literal initializer is outside the subset".to_owned(),
            });
            nctx.env.push(NarrowTarget::Union(UnionTarget {
                name: decl.name.clone(),
                members,
                spelling,
                has_literal_init: false,
            }));
        }
        Some(init) => {
            if !members.iter().any(|(_, id)| *id == init.type_id()) {
                nctx.report.diagnostics.push(PithDiagnostic {
                    code: CODE_MISMATCH.to_owned(),
                    file,
                    span,
                    message: format!(
                        "Type '{}' is not assignable to type '{spelling}'.",
                        init.name()
                    ),
                });
            }
        }
    }
}

/// Checks an `unknown`-annotated declaration's initializer: every shape
/// enters the narrowing environment (probed tsc 7.0.2 P033 — even literal
/// inits refine through guards and diagnose unguarded). Missing and
/// non-literal initializers decline with a note like union targets;
/// bearing literals are clean (`unknown` admits every value, the P025
/// rule), so they enter silently.
fn check_unknown_init(file: FileId, span: Span, decl: &ConstDecl, nctx: &mut NarrowDeclCtx<'_>) {
    match decl.init {
        None => {
            nctx.report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: "missing initializer: nothing to check against".to_owned(),
            });
        }
        Some(InitKind::NonLiteral) => {
            nctx.report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: "non-literal initializer is outside the subset".to_owned(),
            });
        }
        Some(_) => {}
    }
    nctx.env.push(NarrowTarget::Unknown(UnknownTarget {
        name: decl.name.clone(),
    }));
}

/// Fact slices feeding [`check_narrowing`], bundled so the entry point
/// stays lean: identifier uses, `typeof` guards, and decline regions.
#[derive(Debug)]
pub struct NarrowingFacts<'a> {
    /// Identifier uses of union- and `unknown`-annotated consts.
    pub uses: &'a [NarrowedUse],
    /// Straight-line `typeof` guards.
    pub guards: &'a [TypeofGuard],
    /// Spans narrowing refuses to reason inside.
    pub declines: &'a [DeclineRegion],
}

/// Mutable checking state for one [`check_narrowing`] declaration.
struct NarrowDeclCtx<'a> {
    binder: &'a Binder,
    db: &'a mut QueryDb,
    freshness: &'a FreshnessTable,
    env: &'a mut Vec<NarrowTarget>,
    report: &'a mut FileReport,
}

/// Read-only checking state for one [`check_narrowing`] identifier-use.
struct NarrowUseCtx<'a> {
    guards: &'a [TypeofGuard],
    declines: &'a [DeclineRegion],
    env: &'a [NarrowTarget],
    name_counts: &'a HashMap<&'a str, usize>,
    binder: &'a Binder,
    report: &'a mut FileReport,
}
/// One guard's verdict on a use: a single primitive or the full union.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Narrowed {
    /// Refined to one primitive.
    Single(TypeId),
    /// Complement fell outside the union: the full union still applies.
    FullUnion,
}

/// Checks one identifier-use for [`check_narrowing`] (see the routing order
/// on [`check_narrowing`]): link to exactly one target, then refine through
/// decline regions and applicable guards.
fn check_narrowing_use(file: FileId, use_: &NarrowedUse, uctx: &mut NarrowUseCtx<'_>) {
    let linked = link_use_target(
        file,
        use_,
        uctx.env,
        uctx.name_counts,
        uctx.binder,
        &mut *uctx.report,
    );
    let Some(linked) = linked else {
        return;
    };
    refine_use(file, use_, &linked, uctx);
}

/// A use linked to exactly one narrowing target, ready for refinement.
struct LinkedUse<'a> {
    span: Span,
    expected: TypeId,
    expected_text: String,
    target: &'a NarrowTarget,
}

/// Links one identifier-use to its narrowing target: span resolution,
/// expected-type gating, target linkage, ambiguity and literal-init checks.
///
/// Returns `None` when the use declines (one [`UnsupportedDecl`] pushed).
/// Guard refinement runs separately in [`refine_use`].
/// Resolves one narrowing use's expected type: object/union spellings
/// decline, unknown names diagnose `PITH2304`, and `any`/`unknown`
/// expectations accept every narrowed flow silently (probed tsc 7.0.2
/// P033 — silent in every position, for union targets too).
fn resolve_use_expected(
    use_: &NarrowedUse,
    span: Span,
    file: FileId,
    report: &mut FileReport,
) -> Option<TypeId> {
    let expected_text = use_.annotation.trim();
    if expected_text.starts_with('{') {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "non-literal initializer is outside the subset".to_owned(),
        });
        return None;
    }
    if expected_text.contains('|') {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("union annotation '{expected_text}' is outside the subset"),
        });
        return None;
    }
    let expected = match annotation_type(expected_text) {
        Some(id) => id,
        None => match boundary_annotation_type(expected_text) {
            Some(boundary) if boundary == TypeStore::ANY || boundary == TypeStore::UNKNOWN => {
                return None;
            }
            // `never` expectations diagnose like any other `T` (probed
            // P033, both target kinds, guarded and unguarded).
            Some(boundary) if boundary == TypeStore::NEVER => boundary,
            _ => {
                report.diagnostics.push(PithDiagnostic {
                    code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                    file,
                    span,
                    message: format!("Cannot find name '{expected_text}'."),
                });
                return None;
            }
        },
    };
    Some(expected)
}

/// Links one narrowing use to exactly one environment target: unknown
/// targets decline to the legacy note, shadowed/multi-declared targets
/// decline, unresolved-ambiguous targets decline, and literal-initialized
/// union targets decline (tsc never narrows them — probed 7.0.2, while
/// unknown targets always narrow, probed P033).
fn link_target_shape<'a>(
    use_: &NarrowedUse,
    span: Span,
    file: FileId,
    env: &'a [NarrowTarget],
    name_counts: &HashMap<&str, usize>,
    binder: &Binder,
    report: &mut FileReport,
) -> Option<&'a NarrowTarget> {
    let matching: Vec<&NarrowTarget> = env
        .iter()
        .filter(|target| target.name() == use_.target)
        .collect();
    if matching.is_empty() {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "non-literal initializer is outside the subset".to_owned(),
        });
        return None;
    }
    if matching.len() > 1 || name_counts.get(use_.target.as_str()).copied().unwrap_or(0) > 1 {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!(
                "shadowed union target '{}': narrowing needs one declaration",
                use_.target
            ),
        });
        return None;
    }
    let target = matching[0];
    if binder
        .unresolved()
        .iter()
        .any(|entry| entry.file == file && entry.name == use_.target)
    {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!(
                "ambiguous union target '{}': also an unresolved reference",
                use_.target
            ),
        });
        return None;
    }
    // Literal-initialized union targets never narrow (probed tsc 7.0.2);
    // unknown targets always narrow, whatever the initializer (probed P033).
    if let NarrowTarget::Union(union) = target {
        if union.has_literal_init {
            report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: format!(
                    "union target '{}' has a literal initializer: tsc never narrows it (7.0.2)",
                    use_.target
                ),
            });
            return None;
        }
    }
    Some(target)
}

fn link_use_target<'a>(
    file: FileId,
    use_: &NarrowedUse,
    env: &'a [NarrowTarget],
    name_counts: &HashMap<&str, usize>,
    binder: &Binder,
    report: &mut FileReport,
) -> Option<LinkedUse<'a>> {
    let span = binder_span_for(
        binder,
        file,
        use_.name.as_str(),
        use_.scope,
        use_.symbol,
        use_.span,
    );
    let expected = resolve_use_expected(use_, span, file, report)?;
    let target = link_target_shape(use_, span, file, env, name_counts, binder, report)?;
    Some(LinkedUse {
        span,
        expected,
        expected_text: use_.annotation.trim().to_owned(),
        target,
    })
}

/// Refines one linked use through decline regions and applicable guards,
/// dispatching on the target kind (see [`refine_union_use`] and
/// [`refine_unknown_use`]).
fn refine_use(
    file: FileId,
    use_: &NarrowedUse,
    linked: &LinkedUse<'_>,
    uctx: &mut NarrowUseCtx<'_>,
) {
    match linked.target {
        NarrowTarget::Union(target) => refine_union_use(file, use_, linked, target, uctx),
        NarrowTarget::Unknown(target) => refine_unknown_use(file, use_, linked, target, uctx),
    }
}

/// Pushes the decline-region note when the use lies inside a refused
/// region. Returns `true` when the use declines (callers return).
#[must_use]
fn declined_in_region(
    file: FileId,
    span: Span,
    use_: &NarrowedUse,
    declines: &[DeclineRegion],
    report: &mut FileReport,
) -> bool {
    let Some(region) = declines
        .iter()
        .find(|region| span_contains(region.span, use_.init_span))
    else {
        return false;
    };
    report.unsupported.push(UnsupportedDecl {
        file,
        span,
        reason: format!(
            "narrowing declined for use of '{}': {}",
            use_.target, region.reason
        ),
    });
    true
}

/// Which side of one guard a use sits on: `Some(true)` for the
/// matched-literal side (`===` then, `!==` else/after), `Some(false)` for
/// the complement, `None` when the use is outside the guard.
#[must_use]
fn guard_side(guard: &TypeofGuard, init_span: Span) -> Option<bool> {
    // Then of `===` (else of `!==`, after of `!==`) keeps the matched
    // literal; every other branch refines to the complement.
    if span_contains(guard.then_span, init_span) {
        Some(!guard.negated)
    } else if guard
        .else_span
        .is_some_and(|else_span| span_contains(else_span, init_span))
        || guard.early_return && init_span.lo >= guard.if_span.hi
    {
        Some(guard.negated)
    } else {
        None
    }
}

/// Requires every applicable guard to agree on one refinement, defaulting
/// to the full spelling when no guard applies. Returns `None` after pushing
/// the overlap decline.
#[must_use]
fn agree_narrowed(
    narrowed: &[Narrowed],
    file: FileId,
    span: Span,
    target: &str,
    report: &mut FileReport,
) -> Option<Narrowed> {
    if narrowed.is_empty() {
        return Some(Narrowed::FullUnion);
    }
    let first = narrowed[0];
    if narrowed.iter().all(|narrow| *narrow == first) {
        return Some(first);
    }
    report.unsupported.push(UnsupportedDecl {
        file,
        span,
        reason: format!("overlapping guards refine '{target}' differently: outside the subset"),
    });
    None
}

/// Refines one union-linked use through decline regions and applicable
/// guards (the union half of [`refine_use`]).
///
/// Unguarded uses diagnose over the full union spelling; every applicable
/// guard must agree on one primitive (see [`narrow_guard`]).
fn refine_union_use(
    file: FileId,
    use_: &NarrowedUse,
    linked: &LinkedUse<'_>,
    target: &UnionTarget,
    uctx: &mut NarrowUseCtx<'_>,
) {
    let span = linked.span;
    let expected = linked.expected;
    let expected_text = linked.expected_text.as_str();
    let guards = uctx.guards;
    let report: &mut FileReport = &mut *uctx.report;
    if declined_in_region(file, span, use_, uctx.declines, report) {
        return;
    }
    let mut narrowed: Vec<Narrowed> = Vec::new();
    for guard in guards.iter().filter(|guard| guard.target == use_.target) {
        let Some(matched_side) = guard_side(guard, use_.init_span) else {
            continue;
        };
        match narrow_guard(guard, matched_side, target, file, span, report) {
            Ok(narrow) => narrowed.push(narrow),
            Err(()) => return,
        }
    }
    let Some(verdict) = agree_narrowed(&narrowed, file, span, use_.target.as_str(), report) else {
        return;
    };
    match verdict {
        Narrowed::Single(narrowed_id) => {
            if narrowed_id != expected {
                let actual = primitive_name(narrowed_id).unwrap_or("unknown");
                report.diagnostics.push(PithDiagnostic {
                    code: CODE_MISMATCH.to_owned(),
                    file,
                    span,
                    message: format!(
                        "Type '{actual}' is not assignable to type '{expected_text}'."
                    ),
                });
            }
        }
        Narrowed::FullUnion => {
            report.diagnostics.push(PithDiagnostic {
                code: CODE_MISMATCH.to_owned(),
                file,
                span,
                message: format!(
                    "Type '{}' is not assignable to type '{expected_text}'.",
                    target.spelling
                ),
            });
        }
    }
}

/// Refines one `unknown`-linked use through decline regions and applicable
/// guards (the unknown half of [`refine_use`]).
///
/// Matched guard sides refine to the single matched primitive; every other
/// position (unguarded, complements) checks `unknown` — probed tsc 7.0.2
/// P033.
fn refine_unknown_use(
    file: FileId,
    use_: &NarrowedUse,
    linked: &LinkedUse<'_>,
    target: &UnknownTarget,
    uctx: &mut NarrowUseCtx<'_>,
) {
    let span = linked.span;
    let expected = linked.expected;
    let expected_text = linked.expected_text.as_str();
    let report: &mut FileReport = &mut *uctx.report;
    if declined_in_region(file, span, use_, uctx.declines, report) {
        return;
    }
    let mut narrowed: Vec<Narrowed> = Vec::new();
    for guard in uctx
        .guards
        .iter()
        .filter(|guard| guard.target == target.name)
    {
        let Some(matched_side) = guard_side(guard, use_.init_span) else {
            continue;
        };
        match narrow_unknown_guard(guard, matched_side, file, span, report) {
            Ok(narrow) => narrowed.push(narrow),
            Err(()) => return,
        }
    }
    let Some(verdict) = agree_narrowed(&narrowed, file, span, target.name.as_str(), report) else {
        return;
    };
    match verdict {
        Narrowed::Single(narrowed_id) => {
            if narrowed_id != expected {
                let actual = primitive_name(narrowed_id).unwrap_or("unknown");
                report.diagnostics.push(PithDiagnostic {
                    code: CODE_MISMATCH.to_owned(),
                    file,
                    span,
                    message: format!(
                        "Type '{actual}' is not assignable to type '{expected_text}'."
                    ),
                });
            }
        }
        Narrowed::FullUnion => {
            report.diagnostics.push(PithDiagnostic {
                code: CODE_MISMATCH.to_owned(),
                file,
                span,
                message: format!("Type 'unknown' is not assignable to type '{expected_text}'."),
            });
        }
    }
}

/// Applies one guard branch to a use: `matched_side` is `true` for the
/// matched-literal side (`===` then, `!==` else, `!==` after) and `false`
/// for the complement side. `Ok` carries the refinement; `Err` means one
/// [`UnsupportedDecl`] was pushed and the use declines.
fn narrow_guard(
    guard: &TypeofGuard,
    matched_side: bool,
    target: &UnionTarget,
    file: FileId,
    span: Span,
    report: &mut FileReport,
) -> Result<Narrowed, ()> {
    let mut declined = |reason: String| {
        report
            .unsupported
            .push(UnsupportedDecl { file, span, reason });
    };
    let Some(matched) = annotation_type(guard.matched.as_str()) else {
        declined(format!(
            "guard literal '{}' is not a narrowable primitive: outside the subset",
            guard.matched
        ));
        return Err(());
    };
    if guard.matched == "void" {
        declined("typeof never yields 'void': void guards are outside the subset".to_owned());
        return Err(());
    }
    let in_union = target.members.iter().any(|(_, id)| *id == matched);
    if matched_side {
        if !in_union {
            // The region is `never` (silent in tsc): declining keeps the
            // subset from inventing a verdict.
            declined(format!(
                "guard literal '{}' is outside union '{}': the region is never, outside the subset",
                guard.matched, target.spelling
            ));
            return Err(());
        }
        return Ok(Narrowed::Single(matched));
    }
    if !in_union {
        // Complement of an outsider is the full union: check unguarded.
        return Ok(Narrowed::FullUnion);
    }
    let rest: Vec<TypeId> = target
        .members
        .iter()
        .filter(|(_, id)| *id != matched)
        .map(|(_, id)| *id)
        .collect();
    if rest.len() == 1 {
        return Ok(Narrowed::Single(rest[0]));
    }
    declined(format!(
        "complement of '{}' in '{}' is not a single primitive: outside the subset",
        guard.matched, target.spelling
    ));
    Err(())
}

/// Applies one guard branch to an `unknown` use: `matched_side` is `true`
/// for the matched-literal side (`===` then, `!==` else/after) and `false`
/// for the complement. `Ok` carries the refinement; `Err` means one
/// [`UnsupportedDecl`] was pushed and the use declines.
///
/// Unlike [`narrow_guard`], there is no membership test: every primitive is
/// reachable from `unknown`, and every complement falls back to `unknown`
/// (probed tsc 7.0.2 P033: the `else` of `=== "string"` diagnoses
/// `Type 'unknown' …`).
fn narrow_unknown_guard(
    guard: &TypeofGuard,
    matched_side: bool,
    file: FileId,
    span: Span,
    report: &mut FileReport,
) -> Result<Narrowed, ()> {
    let Some(matched) = annotation_type(guard.matched.as_str()) else {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!(
                "guard literal '{}' is not a narrowable primitive: outside the subset",
                guard.matched
            ),
        });
        return Err(());
    };
    if guard.matched == "void" {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "typeof never yields 'void': void guards are outside the subset".to_owned(),
        });
        return Err(());
    }
    if matched_side {
        Ok(Narrowed::Single(matched))
    } else {
        Ok(Narrowed::FullUnion)
    }
}

/// Occurrence [`NodeId`] for the `index`-th synthetic function-return
/// declaration (P013).
///
/// [`check_functions`] delegates to the same [`check_one`] path as
/// [`check_file`], so its memo keys must not alias const-declarator nodes
/// when both check one file against one [`QueryDb`]. Function indices land
/// in a disjoint high range (saturating: skewed inputs pin the top, never
/// wrap into const space).
fn function_occurrence_node(index: usize) -> NodeId {
    const BASE: u32 = 0x4000_0000;
    NodeId(
        u32::try_from(index)
            .unwrap_or(u32::MAX)
            .saturating_add(BASE),
    )
}

/// Saturating declaration index into the occurrence [`NodeId`] key.
///
/// The index is a placeholder occurrence identity until the adapter emits
/// real `NodeId` facts; saturation (never wrapping) keeps skewed inputs
/// from aliasing declaration zero.
fn occurrence_node(index: usize) -> NodeId {
    NodeId(u32::try_from(index).unwrap_or(u32::MAX))
}

/// Declaration span for a const-style declaration in `file`: the exact
/// [`SymbolId`] first, then scope-sensitive [`Binder::resolve`] from the
/// declarator scope, then the caller fallback.
///
/// See [`binder_span_for`] for the resolution contract.
fn binder_span(binder: &Binder, file: FileId, decl: &ConstDecl) -> Span {
    binder_span_for(
        binder,
        file,
        decl.name.as_str(),
        decl.scope,
        decl.symbol,
        decl.span,
    )
}

/// Declaration span for `(name, scope, symbol)` in `file`: the exact
/// [`SymbolId`] first, then scope-sensitive [`Binder::resolve`] from the
/// declarator scope, then the caller fallback.
///
/// The middle step is the P012 fix: resolving from the declarator scope
/// keeps a shadowing inner declaration from verdicting against the outer
/// span (the old name-only lookup always found the first declaration in the
/// file). A `symbol` is trusted only when the store's symbol was declared in
/// the queried file: bare ids are store-relative numbers, so the file check
/// is cheap defense against cross-file laundering. Same-binder ids are
/// authoritative by contract (the driver resolves them from this binder),
/// even ahead of a stale name/scope — see
/// `exact_symbol_identity_beats_scope_lookup`.
///
/// Note the residual contract (not checkable with bare ids): callers must
/// only pass ids resolved from this binder. A foreign id that collides with
/// a same-file local symbol is indistinguishable from the real thing; the
/// e2e drivers always resolve from the checking binder, so this cannot
/// happen on any real path.
fn binder_span_for(
    binder: &Binder,
    file: FileId,
    name: &str,
    scope: u32,
    symbol: Option<SymbolId>,
    fallback: Span,
) -> Span {
    if let Some(id) = symbol {
        if let Some(found) = binder.store().get(id) {
            if found.file == file {
                return found.span;
            }
        }
    }
    binder
        .resolve(file, scope, name)
        .and_then(|id| binder.store().get(id))
        .map_or(fallback, |found| found.span)
}

/// One parsed object-annotation member: name, type text, and whether the
/// name carried `?` (absent uses stay silent while present ones check —
/// probed tsc 7.0.2 P037).
#[derive(Clone, Debug, PartialEq, Eq)]
struct ParsedMember {
    /// Member name with any `?` marker stripped.
    name: String,
    /// Verbatim type text (`"number"`).
    ty: String,
    /// `true` for `y?: number` members.
    optional: bool,
}

/// Parses an object annotation (`{ a: number; b?: string }`) into members in
/// annotation order.
///
/// Separators follow tsc type literals (`;`, `,`, newlines); only plain
/// identifier names parse (a single trailing `?` marks the member
/// optional). Returns `None` for anything outside the subset (missing
/// braces, unparseable or non-identifier members) — never a verdict. An
/// empty `{}` parses to an empty vec; callers decline it separately because
/// tsc skips excess checks against `{}`.
fn parse_object_annotation(text: &str) -> Option<Vec<ParsedMember>> {
    let inner = text.strip_prefix('{')?.strip_suffix('}')?;
    let mut members = Vec::new();
    for piece in inner.split([';', ',', '\n']) {
        let piece = piece.trim();
        if piece.is_empty() {
            continue;
        }
        let (name, ty) = piece.split_once(':')?;
        let (name, optional) = match name.trim().strip_suffix('?') {
            Some(stripped) => (stripped.trim(), true),
            None => (name.trim(), false),
        };
        let ty = ty.trim();
        if name.is_empty()
            || ty.is_empty()
            || !name
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
        {
            return None;
        }
        members.push(ParsedMember {
            name: name.to_owned(),
            ty: ty.to_owned(),
            optional,
        });
    }
    Some(members)
}

/// Classifies one object member's type text: primitive [`TypeId`], or `None`
/// with a flag saying whether the oracle would call it unknown (`TS2304`)
/// versus out-of-subset (union/complex shapes the solver declines).
///
/// Boundary names (`any`, `unknown`, `never`) decline: `any`/`unknown`
/// accept every value in tsc (no per-member verdict exists), while `never`
/// accepts none (unprobed spelling — never forced). Either way the member
/// is recorded, never mis-diagnosed as `TS2304`.
fn classify_member_type(ty: &str) -> Result<TypeId, bool> {
    if boundary_annotation_type(ty).is_some() {
        return Err(false);
    }
    if let Some(id) = annotation_type(ty) {
        return Ok(id);
    }
    // Alphanumeric leftovers are unknown names (oracle `TS2304`); anything
    // with shape syntax is outside the subset (recorded, never diagnosed).
    Err(ty
        .chars()
        .all(|c| c.is_alphanumeric() || c == '_' || c == '$'))
}

/// Spells an object type the way tsc elaborations do: `{ a: number; }`.
/// Members stay in the caller's order (annotation order for expected types,
/// literal order for actual types).
fn object_type_text(names: &[&str], types: &[&str]) -> String {
    debug_assert_eq!(names.len(), types.len());
    if names.is_empty() {
        // tsc spells the empty object type `{}` (probed 7.0.2), never `{ }`.
        return "{}".to_owned();
    }
    let mut text = String::from("{");
    for (name, ty) in names.iter().zip(types.iter()) {
        text.push(' ');
        text.push_str(name);
        text.push_str(": ");
        text.push_str(ty);
        text.push(';');
    }
    text.push_str(" }");
    text
}

/// Checks one declarator, pushing into `report`.
///
/// `node` is the occurrence identity for memo keys and freshness lookups:
/// [`check_file`] passes [`occurrence_node`] positions, [`check_functions`]
/// passes disjoint function nodes — never mix the two for one file.
///
/// `extra` carries cross-file [`Dep`] edges (the declaring file's occurrence
/// nodes a use-file declaration was resolved against): single-file callers
/// pass `&[]`, so their memo entries record exactly today's self-dep.
///
/// Priority inside the object path mirrors tsc (probed 7.0.2): wrong-member
/// `TS2322`s (literal order, one per member) beat the first-excess `TS2353`,
/// which beats missing members (one `TS2741`, or one `TS2739` for several).
/// Only one family ever fires per declaration.
///
/// What assertion application leaves for annotation routing.
enum AssertedInit {
    /// Keep checking with this initializer (`None` = missing).
    Check(Option<InitKind>),
    /// A note was pushed; the declaration is done.
    Done,
}

/// Applies one assertion before annotation routing (probe basis in the
/// `check_one` docs): assertion-plus-object-members is contradictory input;
/// complex casts decline except under `any`; declined casts diagnose and
/// admitted casts substitute — both still check downstream through the
/// returned initializer.
fn apply_assertion(
    decl: &ConstDecl,
    span: Span,
    file: FileId,
    annotation: &str,
    report: &mut FileReport,
) -> AssertedInit {
    let mut init = decl.init;
    let Some(cast) = decl.cast.as_ref() else {
        return AssertedInit::Check(init);
    };
    if decl.init_object.is_some() {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "contradictory initializer facts: assertion with object members".to_owned(),
        });
        return AssertedInit::Done;
    }
    if decl.init_array.is_some() {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "contradictory initializer facts: assertion with array members".to_owned(),
        });
        return AssertedInit::Done;
    }
    match evaluate_cast(cast) {
        CastEvaluation::Complex(reason) => {
            // `any` annotations admit complex casts silently (nothing can
            // mismatch); every other annotation declines with the reason.
            if boundary_annotation_type(annotation) != Some(TypeStore::ANY) {
                report
                    .unsupported
                    .push(UnsupportedDecl { file, span, reason });
            }
            AssertedInit::Done
        }
        CastEvaluation::Decline(result) => {
            emit_cast_diagnostic(file, cast, &mut *report);
            let Some(kind) = result.into_init() else {
                return AssertedInit::Done;
            };
            init = Some(kind);
            AssertedInit::Check(init)
        }
        CastEvaluation::Admit(result) => {
            let Some(kind) = result.into_init() else {
                // Accept-all results (`any`, `never`) silence the
                // position (`never` is assignable to every annotation).
                return AssertedInit::Done;
            };
            init = Some(kind);
            AssertedInit::Check(init)
        }
    }
}

/// The missing-annotation path for `check_one`: declined casts still
/// diagnose without annotations (probed tsc 7.0.2); admitted and complex
/// casts fall into the usual no-annotation decline.
fn decline_unannotated(decl: &ConstDecl, span: Span, file: FileId, report: &mut FileReport) {
    if let Some(cast) = decl.cast.as_ref() {
        if matches!(evaluate_cast(cast), CastEvaluation::Decline(_)) {
            emit_cast_diagnostic(file, cast, &mut *report);
            return;
        }
    }
    report.unsupported.push(UnsupportedDecl {
        file,
        span,
        reason: "no annotation: inference is outside the subset".to_owned(),
    });
}

/// Resolves a boundary annotation (`any`/`unknown`/`never`/unknown names)
/// for `check_one` (probe basis in its docs): `any`/`unknown` admit every
/// bearing value silently and decline missing ones like the primitive path;
/// `never` resolves; anything else unknown diagnoses `PITH2304`.
/// (`any`/`unknown` returned above, so only `None` or `NEVER` arrive at the
/// final match.) Returns the annotation [`TypeId`], or `None` when the
/// declaration is done.
fn resolve_boundary_annotation(
    annotation: &str,
    span: Span,
    file: FileId,
    bearing: bool,
    report: &mut FileReport,
) -> Option<TypeId> {
    if let Some(boundary) = boundary_annotation_type(annotation) {
        if boundary == TypeStore::ANY || boundary == TypeStore::UNKNOWN {
            if bearing {
                return None;
            }
            report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: "missing initializer: nothing to check against".to_owned(),
            });
            return None;
        }
    }
    // `never` carries no [`TypeStore`] primitive in [`annotation_type`], so
    // it resolves here; anything else unknown still diagnoses `PITH2304`.
    let ann_ty = match boundary_annotation_type(annotation) {
        Some(id) if id == TypeStore::NEVER => id,
        _ => {
            let Some(id) = annotation_type(annotation) else {
                report.diagnostics.push(PithDiagnostic {
                    code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                    file,
                    span,
                    message: format!("Cannot find name '{annotation}'."),
                });
                return None;
            };
            id
        }
    };
    Some(ann_ty)
}

/// Rejects contradictory initializer facts for [`check_one`]: at most one
/// of primitive kind, object members, and array members may be present.
/// Returns true when a note was pushed and the declaration is done.
fn check_contradictory_inits(
    decl: &ConstDecl,
    span: Span,
    file: FileId,
    report: &mut FileReport,
) -> bool {
    if decl.init.is_some() && decl.init_object.is_some() {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "contradictory initializer facts: primitive kind with object members"
                .to_owned(),
        });
        return true;
    }
    if decl.init_array.is_some() && (decl.init.is_some() || decl.init_object.is_some()) {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "contradictory initializer facts: array members with \
                another initializer shape"
                .to_owned(),
        });
        return true;
    }
    false
}

/// Finishes a primitive-annotation declaration for [`check_one`]: memoizes
/// the annotation type, then dispatches object/array initializers or checks
/// the literal kind (missing and non-literal initializers decline).
fn finish_primitive_check(
    ann_ty: TypeId,
    init: Option<InitKind>,
    decl: &ConstDecl,
    span: Span,
    annotation: &str,
    ctx: &mut CheckCtx<'_>,
) {
    let file = ctx.file;
    let node = ctx.node;
    let db: &mut QueryDb = &mut *ctx.db;
    let report: &mut FileReport = &mut *ctx.report;
    // Thread through the memo database: the annotation type is the answer
    // to this declaration's TypeOf query; the self-dep plus any cross-file
    // edges let a later edit invalidate exactly the entries that read them.
    let key = QueryKey {
        file,
        node,
        kind: QueryKind::TypeOf,
    };
    let mut deps = Vec::with_capacity(ctx.extra.len().saturating_add(1));
    deps.push(Dep { file, node });
    deps.extend_from_slice(ctx.extra);
    let stored = db.type_of(key, &deps, || ann_ty);
    debug_assert_eq!(stored, ann_ty);
    if let Some(init_object) = decl.init_object.as_ref() {
        check_primitive_annotation_object_init(file, span, annotation, init_object, report);
        return;
    }
    if let Some(init_array) = decl.init_array.as_ref() {
        let mut ctx = CheckCtx {
            file,
            node,
            db,
            freshness: ctx.freshness,
            report,
            extra: ctx.extra,
        };
        check_array_init_vs_annotation(span, annotation, &init_array.members, &mut ctx);
        return;
    }
    let Some(init) = init else {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "missing initializer: nothing to check against".to_owned(),
        });
        return;
    };
    if init == InitKind::NonLiteral {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "non-literal initializer is outside the subset".to_owned(),
        });
        return;
    }
    if init.type_id() != ann_ty {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_MISMATCH.to_owned(),
            file,
            span,
            message: format!(
                "Type '{}' is not assignable to type '{annotation}'.",
                init.name()
            ),
        });
    }
}

/// One single-level local alias expansion step for an annotation.
#[derive(Clone, Debug, PartialEq, Eq)]
enum LocalAliasStep {
    /// No alias claims the name: the existing paths apply.
    Keep,
    /// Alias-to-primitive/boundary: check as if the target were written.
    Primitive(String),
    /// Alias-to-shape: the underlying interface/enum/namespace name, for the
    /// caller to relink (or decline when it holds no shape tables).
    Shape(String),
    /// Unexpandable: chained, generic, circular, complex, duplicate,
    /// shadowed, or unclaimed targets decline with distinct reasons.
    Decline(String),
}

/// Expands one annotation naming a file-local alias, ONE level (mirrors the
/// P035 `expand_imported_alias` rules locally).
///
/// `Keep` means no expansion applies: non-bare spellings, primitive/boundary
/// names (those check directly — aliases can never shadow them), and names
/// no alias claims (the existing unknown-name path applies). Primitives and
/// boundaries rewrite to their spelling; interfaces, enums, and namespaces
/// surface as [`LocalAliasStep::Shape`] for the caller to relink; chains
/// (alias-to-alias), generic aliases, circular references, non-identifier
/// targets, duplicate declarations, and const-shadowed names decline — tsc
/// resolves chains transitively and checks shadowed type meanings, so those
/// declines are pinned divergences.
fn expand_local_alias(scope: &LocalAliasScope<'_, '_>, annotation: &str) -> LocalAliasStep {
    if annotation_type(annotation).is_some()
        || boundary_annotation_type(annotation).is_some()
        || !is_name_segment(annotation)
    {
        return LocalAliasStep::Keep;
    }
    let mut claimed = scope
        .aliases
        .iter()
        .filter(|shape| shape.name == annotation);
    let Some(alias) = claimed.next() else {
        return LocalAliasStep::Keep;
    };
    if claimed.next().is_some() {
        return LocalAliasStep::Decline(format!(
            "multiple type alias declarations for '{annotation}': \
             merging is outside the subset"
        ));
    }
    if scope.const_names.contains(&annotation) {
        return LocalAliasStep::Decline(format!(
            "local value '{annotation}' shadows the type alias: \
             expanding it would hijack a value binding"
        ));
    }
    classify_alias_target(scope.aliases, alias)
}

/// Classifies one claimed alias's target: generics, circularities,
/// primitives/boundaries, complex spellings, chains, or a shape name.
fn classify_alias_target(aliases: &[TypeAliasShape], alias: &TypeAliasShape) -> LocalAliasStep {
    if alias.has_type_params {
        return LocalAliasStep::Decline(format!(
            "type alias '{}' is generic: generic aliases are outside the subset",
            alias.name
        ));
    }
    let target = alias.target.trim();
    if target.is_empty() || target == alias.name {
        return LocalAliasStep::Decline(format!(
            "type alias '{}' is circular: circular aliases are outside the subset",
            alias.name
        ));
    }
    if annotation_type(target).is_some() || boundary_annotation_type(target).is_some() {
        return LocalAliasStep::Primitive(target.to_owned());
    }
    if !is_name_segment(target) {
        return LocalAliasStep::Decline(format!(
            "type alias '{}' targets '{target}': \
             non-identifier alias targets are outside the subset",
            alias.name
        ));
    }
    if aliases.iter().any(|shape| shape.name == target) {
        return LocalAliasStep::Decline(format!(
            "type alias '{}' targets '{target}': \
             chained aliases are outside the subset (single-level expansion only)",
            alias.name
        ));
    }
    LocalAliasStep::Shape(target.to_owned())
}

/// Decline reason for a generic-alias instantiation head (`Box` in
/// `Box<number>`): only generic heads decline here — every other head keeps
/// the existing verdict path (a raw check would add a misleading `PITH2304`
/// where tsc stays clean).
fn generic_head_decline(scope: &LocalAliasScope<'_, '_>, annotation: &str) -> Option<String> {
    let (head, _) = annotation.split_once('<')?;
    if let LocalAliasStep::Decline(reason) = expand_local_alias(scope, head.trim()) {
        return Some(reason);
    }
    None
}

/// One same-file shape lookup for an alias target, by name.
#[derive(Clone, Debug, PartialEq)]
enum LocalShapeHit<'a> {
    /// Exactly one interface bears the name.
    Interface(&'a InterfaceShape),
    /// Exactly one enum bears the name (no interface does).
    Enum(&'a EnumShape),
    /// A namespace bears the name (no interface or enum does).
    Namespace,
    /// Several interfaces or several enums bear the name: merging is
    /// outside the subset (the multiple-declaration precedent).
    Multiple(String),
    /// No shape bears the name.
    Absent,
}

/// Finds one same-file shape by name for alias relinking: enums before
/// interfaces (the [`EnumDeclCtx::claim`] order — merged enum+interface
/// pairs are illegal in tsc), namespaces last.
fn find_local_shape<'m>(input: &'m EnumInput<'_>, target: &str) -> LocalShapeHit<'m> {
    if input
        .enums
        .iter()
        .filter(|shape| shape.name == target)
        .count()
        > 1
    {
        return LocalShapeHit::Multiple(format!(
            "multiple enum declarations for '{target}': merging is outside the subset"
        ));
    }
    if let Some(shape) = input.enums.iter().find(|shape| shape.name == target) {
        return LocalShapeHit::Enum(shape);
    }
    if input
        .interfaces
        .iter()
        .filter(|shape| shape.name == target)
        .count()
        > 1
    {
        return LocalShapeHit::Multiple(format!(
            "multiple interface declarations for '{target}': merging is outside the subset"
        ));
    }
    if let Some(shape) = input.interfaces.iter().find(|shape| shape.name == target) {
        return LocalShapeHit::Interface(shape);
    }
    if input.namespaces.iter().any(|shape| shape.name == target) {
        return LocalShapeHit::Namespace;
    }
    LocalShapeHit::Absent
}

/// Outcome of [`expand_local_annotation`]: the caller either returns
/// (decline pushed), keeps the original spelling, or checks the rewritten
/// spelling. A custom enum because clippy forbids `Option<Option<_>>`.
enum LocalAnnotation {
    /// Decline note pushed; the caller returns.
    Done,
    /// Keep the original annotation spelling.
    Keep,
    /// Rewritten (primitive/boundary target) spelling.
    Rewritten(String),
}

/// Local alias expansion step for [`check_one`]: bare alias names rewrite
/// (primitives/boundaries) or decline, and generic-instantiation heads
/// decline, so the boundary path never invents a `PITH2304` for them.
/// Sits after the promise/array/union/lib gates so those spellings keep
/// their verdicts.
fn expand_local_annotation(
    scope: &LocalAliasScope<'_, '_>,
    annotation: &str,
    file: FileId,
    span: Span,
    report: &mut FileReport,
) -> LocalAnnotation {
    match expand_local_alias(scope, annotation) {
        LocalAliasStep::Keep => {
            if let Some(reason) = generic_head_decline(scope, annotation) {
                report
                    .unsupported
                    .push(UnsupportedDecl { file, span, reason });
                return LocalAnnotation::Done;
            }
            LocalAnnotation::Keep
        }
        LocalAliasStep::Primitive(spelling) => LocalAnnotation::Rewritten(spelling),
        LocalAliasStep::Shape(target) => {
            report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: format!(
                    "annotation '{annotation}' is a local alias for '{target}': \
                     named-shape aliases check through the interface/enum paths"
                ),
            });
            LocalAnnotation::Done
        }
        LocalAliasStep::Decline(reason) => {
            report
                .unsupported
                .push(UnsupportedDecl { file, span, reason });
            LocalAnnotation::Done
        }
    }
}

/// Takes the shared [`CheckCtx`] (file, node, memo store, freshness table,
/// report, and extra cross-file edges) so the arity stays flat as the
/// subset grows; `binder` and `decl` ride alongside.
fn check_one(
    decl: &ConstDecl,
    binder: &Binder,
    ctx: &mut CheckCtx<'_>,
    scope: &LocalAliasScope<'_, '_>,
) {
    let file = ctx.file;
    let node = ctx.node;
    let db: &mut QueryDb = &mut *ctx.db;
    let freshness = ctx.freshness;
    let report: &mut FileReport = &mut *ctx.report;
    let extra = ctx.extra;
    let span = binder_span(binder, file, decl);
    let Some(raw) = decl.annotation.as_deref() else {
        decline_unannotated(decl, span, file, &mut *report);
        return;
    };
    let annotation = raw.trim();
    if check_contradictory_inits(decl, span, file, &mut *report) {
        return;
    }
    // Assertion evaluation runs before annotation routing (see
    // `apply_assertion`): declined casts diagnose independently of the
    // annotation while admitted results substitute the initializer kind.
    let init = match apply_assertion(decl, span, file, annotation, &mut *report) {
        AssertedInit::Check(init) => init,
        AssertedInit::Done => return,
    };
    if annotation.starts_with('{') {
        let mut ctx = CheckCtx {
            file,
            node,
            db,
            freshness,
            report,
            extra,
        };
        if let Some(init_array) = decl.init_array.as_ref() {
            check_object_annotation_array_init(span, annotation, &init_array.members, &mut ctx);
            return;
        }
        check_object(decl, span, annotation, init, &mut ctx);
        return;
    }
    if let Some(array) = classify_array_annotation(annotation) {
        let mut ctx = CheckCtx {
            file,
            node,
            db,
            freshness,
            report,
            extra,
        };
        check_array_annotation(decl, span, &array, init, &mut ctx);
        return;
    }
    if let Some(promise) = classify_promise_annotation(annotation) {
        let reason = match &promise {
            PromiseAnnotation::Admit(inner) => format!(
                "promise annotation '{annotation}' on a const-style declaration: \
                only async function returns carry promise values (unwraps to '{}')",
                inner.spelling()
            ),
            PromiseAnnotation::Decline(reason) => reason.clone(),
        };
        report
            .unsupported
            .push(UnsupportedDecl { file, span, reason });
        return;
    }
    if annotation.contains('|') {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("union annotation '{annotation}' is outside the subset"),
        });
        return;
    }
    if let Some(reason) = lib_decline_reason(annotation) {
        report
            .unsupported
            .push(UnsupportedDecl { file, span, reason });
        return;
    }
    // Local alias expansion sits after the promise/array/union/lib gates
    // so those spellings keep their verdicts (see
    // `expand_local_annotation`).
    let rewritten = match expand_local_annotation(scope, annotation, file, span, &mut *report) {
        LocalAnnotation::Done => return,
        LocalAnnotation::Keep => None,
        LocalAnnotation::Rewritten(spelling) => Some(spelling),
    };
    let annotation: &str = rewritten.as_deref().unwrap_or(annotation);
    // Boundary annotations (probed tsc 7.0.2 — see
    // `resolve_boundary_annotation`): bearing means any initializer shape,
    // object or array members, or assertion facts are present.
    let bearing = init.is_some()
        || decl.init_object.is_some()
        || decl.init_array.is_some()
        || decl.cast.is_some();
    let Some(ann_ty) = resolve_boundary_annotation(annotation, span, file, bearing, &mut *report)
    else {
        return;
    };
    // Thread through the memo database: the annotation type is the answer
    // to this declaration's TypeOf query (see `finish_primitive_check`).
    let mut tail = CheckCtx {
        file,
        node,
        db: &mut *db,
        freshness,
        report: &mut *report,
        extra,
    };
    finish_primitive_check(ann_ty, init, decl, span, annotation, &mut tail);
}

/// Primitive annotation with an object-literal initializer (oracle spells
/// `Type '{ a: number; }' is not assignable to type 'number'.`).
///
/// Non-literal members cannot be spelled, so they decline to unsupported
/// instead of diagnosing.
fn check_primitive_annotation_object_init(
    file: FileId,
    span: Span,
    annotation: &str,
    init_object: &ObjectInit,
    report: &mut FileReport,
) {
    let mut names: Vec<&str> = Vec::with_capacity(init_object.members.len());
    let mut types: Vec<&str> = Vec::with_capacity(init_object.members.len());
    for member in &init_object.members {
        if member.kind == ObjectMemberKind::NonLiteral {
            report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: format!("non-literal member '{}' is outside the subset", member.name),
            });
            return;
        }
        names.push(member.name.as_str());
        types.push(member.kind.display_name());
    }
    report.diagnostics.push(PithDiagnostic {
        code: CODE_MISMATCH.to_owned(),
        file,
        span,
        message: format!(
            "Type '{}' is not assignable to type '{annotation}'.",
            object_type_text(&names, &types)
        ),
    });
}

/// Shared checking context: occurrence identity plus the verdict sinks.
///
/// Bundles the parameters every object-check helper needs so arity stays
/// flat as the subset grows. `extra` carries cross-file [`Dep`] edges (see
/// [`check_one`]); the object-shape memo records them alongside the self-dep.
struct CheckCtx<'a> {
    file: FileId,
    node: NodeId,
    db: &'a mut QueryDb,
    freshness: &'a FreshnessTable,
    report: &'a mut FileReport,
    extra: &'a [Dep],
}

/// Object annotation (`{ a: number; ... }`) against any initializer.
///
/// Member-type failures diagnose unknown names (`TS2304`) or decline the
/// rest (union/complex shapes) before any shape comparison; the shape
/// comparison itself fires exactly one diagnostic family per declaration
/// (wrong > excess > missing). See the module-level object rules.
fn check_object(
    decl: &ConstDecl,
    span: Span,
    annotation: &str,
    init: Option<InitKind>,
    ctx: &mut CheckCtx<'_>,
) {
    let Some(parsed) = parse_object_members(annotation, span, ctx) else {
        return;
    };
    let Some(expected) = classify_expected(&parsed, span, ctx) else {
        return;
    };
    let expected_text = expected_object_text(&expected);
    finish_object_check(decl, span, &expected, &expected_text, init, ctx);
}

/// Shared object-literal comparison tail: memoizes the shape, then fires
/// the single-family comparison (or the non-object-init path) with
/// `expected_text` as the expected-type spelling — the `{...}` expansion
/// for inline annotations, the bare interface name for
/// [`check_interface_shape`] (probed tsc 7.0.2: interface elaborations
/// spell the name, never expanded members).
///
/// `init` is the initializer kind to compare: the declaration's own kind,
/// or the cast-substituted kind when [`check_one`] evaluated an assertion
/// (assertions never pair with object members, so the substitution only
/// ever reaches the non-object path).
fn finish_object_check(
    decl: &ConstDecl,
    span: Span,
    expected: &[ExpectedMember],
    expected_text: &str,
    init: Option<InitKind>,
    ctx: &mut CheckCtx<'_>,
) {
    memoize_object_shape(expected, ctx);
    match decl.init_object.as_ref() {
        None => check_object_annotation_non_object_init(init, span, expected_text, ctx),
        Some(init_object) => {
            compare_object_members(span, expected, expected_text, init_object, ctx);
        }
    }
}

/// Parses an object annotation into [`ParsedMember`]s (name, type text,
/// optionality), declining unparseable shapes and empty `{}` (tsc skips
/// excess checks against `{}`).
fn parse_object_members(
    annotation: &str,
    span: Span,
    ctx: &mut CheckCtx<'_>,
) -> Option<Vec<ParsedMember>> {
    let Some(parsed) = parse_object_annotation(annotation) else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: format!("object annotation '{annotation}' is outside the subset"),
        });
        return None;
    };
    if parsed.is_empty() {
        // tsc skips excess checks against `{}` (probed 7.0.2: `{ a: 1 }`
        // assigns cleanly), so diagnosing here would force a divergence.
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "empty object annotation is outside the subset".to_owned(),
        });
        return None;
    }
    Some(parsed)
}

/// One classified annotation member: name, primitive type, display text for
/// messages, and whether absent uses stay silent (P037 optional members).
#[derive(Clone, Debug)]
struct ExpectedMember {
    /// Member name as written in the annotation.
    name: String,
    /// Builtin [`TypeId`] present members compare against.
    id: TypeId,
    /// Plain type text for `TS2322` messages (`"number"` — never the
    /// `| undefined` elaboration, which only missing/excess texts spell).
    display: String,
    /// `true` for `y?: number` members (absent silent, present checked).
    optional: bool,
}

/// Resolves every member type to a primitive: unknown names diagnose
/// (`TS2304`, one per name), union/complex shapes decline the declaration.
/// Optionality rides along untouched: it gates missing-member silence and
/// the expected-type spelling, never the type comparison itself.
fn classify_expected(
    parsed: &[ParsedMember],
    span: Span,
    ctx: &mut CheckCtx<'_>,
) -> Option<Vec<ExpectedMember>> {
    let mut expected: Vec<ExpectedMember> = Vec::with_capacity(parsed.len());
    let mut unknown: Vec<&str> = Vec::new();
    for member in parsed {
        let (name, ty) = (member.name.as_str(), member.ty.as_str());
        match classify_member_type(ty) {
            Ok(id) => expected.push(ExpectedMember {
                name: name.to_owned(),
                id,
                display: ty.to_owned(),
                optional: member.optional,
            }),
            Err(is_unknown) => {
                if is_unknown {
                    unknown.push(ty);
                } else {
                    let reason = if ty.contains('|') {
                        format!("union member type '{ty}' is outside the subset")
                    } else {
                        format!("member type '{ty}' for '{name}' is outside the subset")
                    };
                    ctx.report.unsupported.push(UnsupportedDecl {
                        file: ctx.file,
                        span,
                        reason,
                    });
                    return None;
                }
            }
        }
    }
    if !unknown.is_empty() {
        for name in unknown {
            ctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                file: ctx.file,
                span,
                message: format!("Cannot find name '{name}'."),
            });
        }
        return None;
    }
    Some(expected)
}

/// Threads the interned object shape through the memo database like the
/// primitive path: structure interns globally in the shared store, freshness
/// stays in the occurrence table (H-002).
fn memoize_object_shape(expected: &[ExpectedMember], ctx: &mut CheckCtx<'_>) {
    let shape = TypeData::Object {
        members: expected
            .iter()
            .map(|member| (member.name.clone(), member.id))
            .collect(),
    };
    let ann_ty = ctx.db.types_mut().intern(shape);
    let key = QueryKey {
        file: ctx.file,
        node: ctx.node,
        kind: QueryKind::TypeOf,
    };
    let mut deps = Vec::with_capacity(ctx.extra.len().saturating_add(1));
    deps.push(Dep {
        file: ctx.file,
        node: ctx.node,
    });
    deps.extend_from_slice(ctx.extra);
    let stored = ctx.db.type_of(key, &deps, || ann_ty);
    debug_assert_eq!(stored, ann_ty);
}

/// Literal members in literal order; duplicate names fold last-wins
/// (same-shape duplicates verdict identically either way).
fn collect_actual(init_object: &ObjectInit) -> Vec<(String, ObjectMemberKind)> {
    let mut actual: Vec<(String, ObjectMemberKind)> = Vec::with_capacity(init_object.members.len());
    for member in &init_object.members {
        if let Some(slot) = actual.iter_mut().find(|slot| slot.0 == member.name) {
            slot.1 = member.kind;
        } else {
            actual.push((member.name.clone(), member.kind));
        }
    }
    actual
}

/// Compares one fresh-literal shape against its annotation, firing at most
/// one family: wrong members first, then first-excess (freshness-gated),
/// then missing members.
fn compare_object_members(
    span: Span,
    expected: &[ExpectedMember],
    expected_text: &str,
    init_object: &ObjectInit,
    ctx: &mut CheckCtx<'_>,
) {
    let actual = collect_actual(init_object);
    if let Some(name) = actual
        .iter()
        .find(|(_, kind)| *kind == ObjectMemberKind::NonLiteral)
        .map(|(name, _)| name.clone())
    {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: format!("non-literal member '{name}' is outside the subset"),
        });
        return;
    }
    if diagnose_wrong_members(span, expected, &actual, ctx) {
        return;
    }
    if diagnose_excess_member(span, expected, expected_text, &actual, ctx) {
        return;
    }
    diagnose_missing_members(span, expected, expected_text, &actual, ctx);
}

/// Wrong members (literal order, one `TS2322` each): they suppress every
/// other family (probed 7.0.2). Returns whether any fired.
fn diagnose_wrong_members(
    span: Span,
    expected: &[ExpectedMember],
    actual: &[(String, ObjectMemberKind)],
    ctx: &mut CheckCtx<'_>,
) -> bool {
    let mut wrong: Vec<(&str, &str)> = Vec::new();
    for (name, kind) in actual {
        let Some(entry) = expected
            .iter()
            .find(|entry| entry.name.as_str() == name.as_str())
        else {
            continue;
        };
        if kind.type_id() != entry.id {
            wrong.push((kind.widened_name(), entry.display.as_str()));
        }
    }
    if wrong.is_empty() {
        return false;
    }
    for (actual_ty, expected_ty) in wrong {
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_MISMATCH.to_owned(),
            file: ctx.file,
            span,
            message: format!("Type '{actual_ty}' is not assignable to type '{expected_ty}'."),
        });
    }
    true
}

/// First excess member, gated on per-occurrence freshness: only a positively
/// fresh literal may diagnose; anything else declines with the freshness
/// reason instead of forcing a verdict. Returns whether the family fired
/// (diagnosis or decline).
fn diagnose_excess_member(
    span: Span,
    expected: &[ExpectedMember],
    expected_text: &str,
    actual: &[(String, ObjectMemberKind)],
    ctx: &mut CheckCtx<'_>,
) -> bool {
    let Some(first) = actual
        .iter()
        .map(|(name, _)| name.as_str())
        .find(|name| expected.iter().all(|entry| entry.name != *name))
    else {
        return false;
    };
    if ctx.freshness.is_fresh(ctx.file, ctx.node) {
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_EXCESS_MEMBER.to_owned(),
            file: ctx.file,
            span,
            message: format!(
                "Object literal may only specify known properties, and '{first}' does not exist in type '{expected_text}'."
            ),
        });
    } else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "stale object literal: excess-property checks need a fresh literal".to_owned(),
        });
    }
    true
}

/// Missing members (annotation order, required only): one is `TS2741`,
/// several collapse into one `TS2739`. Optional members are invisible here:
/// absent uses stay silent (probed tsc 7.0.2 P037).
fn diagnose_missing_members(
    span: Span,
    expected: &[ExpectedMember],
    expected_text: &str,
    actual: &[(String, ObjectMemberKind)],
    ctx: &mut CheckCtx<'_>,
) {
    let actual_text = object_type_text(
        &actual
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<&str>>(),
        &actual
            .iter()
            .map(|(_, kind)| kind.display_name())
            .collect::<Vec<&str>>(),
    );
    let missing: Vec<&str> = expected
        .iter()
        .filter(|member| !member.optional)
        .map(|member| member.name.as_str())
        .filter(|name| actual.iter().all(|slot| slot.0 != *name))
        .collect();
    emit_missing(
        ctx.file,
        &MissingEmission {
            span,
            expected_text,
            actual_text,
            missing,
        },
        &mut *ctx.report,
    );
}

/// Object annotation with a non-object initializer.
///
/// Primitive literals diagnose compositionally (oracle: `Type 'number' is
/// not assignable to type '{ a: number; }'.`); missing/non-literal
/// initializers decline with the usual reasons. `init` is the declaration's
/// own kind or the cast-substituted kind (see [`finish_object_check`]).
fn check_object_annotation_non_object_init(
    init: Option<InitKind>,
    span: Span,
    expected_text: &str,
    ctx: &mut CheckCtx<'_>,
) {
    let Some(init) = init else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "missing initializer: nothing to check against".to_owned(),
        });
        return;
    };
    if init == InitKind::NonLiteral {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "non-literal initializer is outside the subset".to_owned(),
        });
        return;
    }
    ctx.report.diagnostics.push(PithDiagnostic {
        code: CODE_MISMATCH.to_owned(),
        file: ctx.file,
        span,
        message: format!(
            "Type '{}' is not assignable to type '{expected_text}'.",
            init.name()
        ),
    });
}

/// Spells one array initializer the way tsc elaborations do: `never[]` for
/// empty, `number[]` for uniform literals.
///
/// Returns `None` for unspellable shapes — any non-literal element (no
/// value-type facts) or mixed literal kinds (tsc spells unions like
/// `(string | number)[]`, which the subset refuses): the caller declines
/// instead of mis-spelling.
fn spell_array_actual(members: &[ArrayMemberKind]) -> Option<String> {
    if members.is_empty() {
        return Some("never[]".to_owned());
    }
    let mut spelling: Option<&str> = None;
    for member in members {
        if *member == ArrayMemberKind::NonLiteral {
            return None;
        }
        let name = member.widened_name();
        match spelling {
            None => spelling = Some(name),
            Some(known) if known == name => {}
            Some(_) => return None,
        }
    }
    spelling.map(|name| format!("{name}[]"))
}

/// Array annotation with an admitted element type against any initializer.
///
/// Array declarations skip the [`QueryDb`] memo: [`TypeData`] has no array
/// shape (and `pith-types` is outside this task's scope), so there is
/// nothing sound to intern — the enum precedent. Always safe, just less
/// incremental.
fn check_array_admitted(
    decl: &ConstDecl,
    span: Span,
    element: &ArrayElement,
    init: Option<InitKind>,
    ctx: &mut CheckCtx<'_>,
) {
    match decl.init_array.as_ref() {
        Some(init_array) => {
            check_array_members(span, element, &init_array.members, ctx);
        }
        None => check_array_annotation_non_array_init(init, span, element, ctx),
    }
}

/// Routes one array spelling: declines carry their reason; admitted
/// elements check through [`check_array_admitted`].
fn check_array_annotation(
    decl: &ConstDecl,
    span: Span,
    array: &ArrayAnnotation,
    init: Option<InitKind>,
    ctx: &mut CheckCtx<'_>,
) {
    match array {
        ArrayAnnotation::Decline(reason) => {
            ctx.report.unsupported.push(UnsupportedDecl {
                file: ctx.file,
                span,
                reason: reason.clone(),
            });
        }
        ArrayAnnotation::Admit(element) => {
            check_array_admitted(decl, span, element, init, ctx);
        }
    }
}

/// Verifies array-literal members one by one against the element type.
///
/// Each mismatched member diagnoses `TS2322` in literal order (probed
/// 7.0.2); non-literal members skip silently (probed clean); `any`/`unknown`
/// elements admit everything silently.
fn check_array_members(
    span: Span,
    element: &ArrayElement,
    members: &[ArrayMemberKind],
    ctx: &mut CheckCtx<'_>,
) {
    if element.id == TypeStore::ANY || element.id == TypeStore::UNKNOWN {
        return;
    }
    for member in members {
        if *member == ArrayMemberKind::NonLiteral {
            continue;
        }
        if member.type_id() != element.id {
            ctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_MISMATCH.to_owned(),
                file: ctx.file,
                span,
                message: format!(
                    "Type '{}' is not assignable to type '{}'.",
                    member.widened_name(),
                    element.spelling
                ),
            });
        }
    }
}

/// Array annotation with a non-array initializer.
///
/// Missing/non-literal initializers decline with the usual reasons;
/// primitive literals diagnose compositionally with the suffix spelling
/// (`Type 'number' is not assignable to type 'number[]'.`, probed 7.0.2).
fn check_array_annotation_non_array_init(
    init: Option<InitKind>,
    span: Span,
    element: &ArrayElement,
    ctx: &mut CheckCtx<'_>,
) {
    let Some(init) = init else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "missing initializer: nothing to check against".to_owned(),
        });
        return;
    };
    if init == InitKind::NonLiteral {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "non-literal initializer is outside the subset".to_owned(),
        });
        return;
    }
    ctx.report.diagnostics.push(PithDiagnostic {
        code: CODE_MISMATCH.to_owned(),
        file: ctx.file,
        span,
        message: format!(
            "Type '{}' is not assignable to type '{}[]'.",
            init.name(),
            element.spelling
        ),
    });
}

/// Array initializer against a primitive/`never` annotation.
///
/// Diagnoses with the spelled actual (`number[]`, `never[]` for empty);
/// unspellable shapes decline instead of mis-spelling.
fn check_array_init_vs_annotation(
    span: Span,
    annotation: &str,
    members: &[ArrayMemberKind],
    ctx: &mut CheckCtx<'_>,
) {
    let Some(actual) = spell_array_actual(members) else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "array initializer has no single spellable element type: \
                unions need value facts outside the subset"
                .to_owned(),
        });
        return;
    };
    ctx.report.diagnostics.push(PithDiagnostic {
        code: CODE_MISMATCH.to_owned(),
        file: ctx.file,
        span,
        message: format!("Type '{actual}' is not assignable to type '{annotation}'."),
    });
}

/// Inputs for one missing-member emission: expected/actual spellings plus
/// the missing names in annotation order.
struct MissingEmission<'a> {
    /// Declaration span the diagnostic points at.
    span: Span,
    /// Expected-type spelling (expanded `{ ... }` or an interface name).
    expected_text: &'a str,
    /// Actual-type spelling (expanded `{ ... }` or a spelled array).
    actual_text: String,
    /// Missing member names in annotation order.
    missing: Vec<&'a str>,
}

/// Emits one missing-member family: one member is `TS2741`, several
/// collapse into one `TS2739` (probed 7.0.2).
fn emit_missing(file: FileId, emission: &MissingEmission<'_>, report: &mut FileReport) {
    if emission.missing.len() == 1 {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_MISSING_MEMBER.to_owned(),
            file,
            span: emission.span,
            message: format!(
                "Property '{}' is missing in type '{}' but required in type '{}'.",
                emission.missing[0], emission.actual_text, emission.expected_text
            ),
        });
    } else if !emission.missing.is_empty() {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_MISSING_MANY.to_owned(),
            file,
            span: emission.span,
            message: format!(
                "Type '{}' is missing the following properties from type '{}': {}",
                emission.actual_text,
                emission.expected_text,
                emission.missing.join(", ")
            ),
        });
    }
}

/// Spells the expected object type in annotation order (the shared
/// elaboration for inline annotations): `{ a: number; }`, with optional
/// members spelled exactly like tsc (`y?: number | undefined` — probed
/// 7.0.2 P037).
fn expected_object_text(expected: &[ExpectedMember]) -> String {
    if expected.is_empty() {
        // tsc spells the empty object type `{}` (probed 7.0.2), never `{ }`.
        return "{}".to_owned();
    }
    let mut text = String::from("{");
    for member in expected {
        text.push(' ');
        text.push_str(member.name.as_str());
        if member.optional {
            text.push('?');
        }
        text.push_str(": ");
        text.push_str(member.display.as_str());
        if member.optional {
            text.push_str(" | undefined");
        }
        text.push(';');
    }
    text.push_str(" }");
    text
}

/// Array initializer against an object annotation: tsc reports the missing
/// family with the array spelling as the actual type (`Property 'x' is
/// missing in type 'number[]' but required in type '{ x: number; }'.`,
/// probed 7.0.2). Arrays carry no named members, so every REQUIRED expected
/// member is missing (optional members stay silent — probed P037);
/// unspellable arrays decline.
fn check_object_annotation_array_init(
    span: Span,
    annotation: &str,
    members: &[ArrayMemberKind],
    ctx: &mut CheckCtx<'_>,
) {
    let Some(parsed) = parse_object_members(annotation, span, ctx) else {
        return;
    };
    let Some(expected) = classify_expected(&parsed, span, ctx) else {
        return;
    };
    let expected_text = expected_object_text(&expected);
    let Some(actual) = spell_array_actual(members) else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "array initializer has no single spellable element type: \
                unions need value facts outside the subset"
                .to_owned(),
        });
        return;
    };
    let missing: Vec<&str> = expected
        .iter()
        .filter(|member| !member.optional)
        .map(|member| member.name.as_str())
        .collect();
    emit_missing(
        ctx.file,
        &MissingEmission {
            span,
            expected_text: expected_text.as_str(),
            actual_text: actual,
            missing,
        },
        &mut *ctx.report,
    );
}

/// One heritage parent of an interface: name plus span.
///
/// Driver-mapped from the adapter's `InterfaceHeritageFact` (mechanical
/// field copy). Names feed decline reasons only — heritage is outside the
/// subset, so no verdict ever reads them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceHeritage {
    /// Parent name as written (`"Base"`).
    pub name: String,
    /// Span of the heritage clause.
    pub span: Span,
}

/// One interface member: name plus annotation text.
///
/// Driver-mapped from the adapter's `InterfaceMemberFact` (mechanical field
/// copy). `complex_reason` carries the adapter's decline marker verbatim;
/// checkable members carry the raw annotation text for
/// [`classify_expected`], and `optional` marks `y?: T` members (absent uses
/// silent, present checked — probed tsc 7.0.2 P037).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceMember {
    /// Member name as written.
    pub name: String,
    /// Raw annotation text (`Some("number")`); `None` when absent.
    pub annotation_text: Option<String>,
    /// `true` for `y?: T` members.
    pub optional: bool,
    /// Span of the member signature.
    pub span: Span,
    /// Adapter decline marker; `Some` means the interface declines.
    pub complex_reason: Option<String>,
}

/// One `interface` declaration available as an annotation target.
///
/// Driver-mapped from the adapter's `InterfaceFact` (mechanical field copy,
/// plus the binder [`SymbolId`] resolved from the same [`Binder`] used for
/// checking — the linkage that makes merged interface+value pairs resolve).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceShape {
    /// Interface name as written.
    pub name: String,
    /// Per-file scope index of the declaration (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity resolved from the checking [`Binder`]; shapes
    /// with `None` never match (the driver must link — asserted in tests).
    pub symbol: Option<SymbolId>,
    /// Whole-declaration span.
    pub span: Span,
    /// Member facts in source order.
    pub members: Vec<InterfaceMember>,
    /// Heritage parents; non-empty declines.
    pub heritage: Vec<InterfaceHeritage>,
    /// `true` when the interface declares type parameters: declines.
    pub has_type_params: bool,
    /// Whether the declaration was exported (gates qualified visibility,
    /// except inside ambient namespaces).
    pub exported: bool,
}

/// One enum member's constant value: literal values feed membership checks;
/// computed members decline the whole enum with their reason.
#[derive(Clone, Debug, PartialEq)]
pub enum EnumMemberValue {
    /// A numeric literal initializer: the parsed value.
    Number(f64),
    /// A string literal initializer: the unescaped value (never matches a
    /// literal — probed tsc 7.0.2 — but rides along for shape fidelity).
    String(String),
    /// Any non-literal initializer, missing increment base, or computed
    /// member name: the solver declines enums holding one of these.
    Computed {
        /// Why no value is recorded (from the adapter's fact).
        reason: String,
    },
}

/// One enum member: name plus constant value.
///
/// Driver-mapped from the adapter's `EnumMemberFact` (mechanical field copy).
#[derive(Clone, Debug, PartialEq)]
pub struct EnumMember {
    /// Member name as written.
    pub name: String,
    /// Constant value, or the decline reason when uncomputable.
    pub value: EnumMemberValue,
    /// Span of the whole member.
    pub span: Span,
}

/// One `enum` declaration available as an annotation target.
///
/// Driver-mapped from the adapter's `EnumFact` (mechanical field copy, plus
/// the binder [`SymbolId`] resolved from the same [`Binder`] used for
/// checking). `is_const` never forks checking (probed identical);
/// `declared` (ambient) declines; `exported` gates qualified visibility.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumShape {
    /// Enum name as written.
    pub name: String,
    /// Per-file scope index of the declaration (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity resolved from the checking [`Binder`]; shapes
    /// with `None` never match (the driver must link — asserted in tests).
    pub symbol: Option<SymbolId>,
    /// Whole-declaration span.
    pub span: Span,
    /// Member facts in source order.
    pub members: Vec<EnumMember>,
    /// `true` for `const enum` (recorded only: checking is identical).
    pub is_const: bool,
    /// `true` for `declare enum` (ambient): the solver declines.
    pub declared: bool,
    /// Whether the declaration was exported (gates qualified visibility,
    /// except inside ambient namespaces).
    pub exported: bool,
}

/// One `namespace`/`module` block available as a qualification head.
///
/// Driver-mapped from the adapter's `NamespaceFact` (mechanical field copy,
/// plus the binder [`SymbolId`] resolved from the same [`Binder`] used for
/// checking). Tail members resolve from `body_scope` through the
/// [`Binder`]; `declared` (ambient) lifts the export gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamespaceShape {
    /// Block name as written.
    pub name: String,
    /// Per-file scope index of the declaration (from the adapter's facts).
    pub scope: u32,
    /// Exact binder identity resolved from the checking [`Binder`]; shapes
    /// with `None` never match (the driver must link — asserted in tests).
    pub symbol: Option<SymbolId>,
    /// Whole-declaration span.
    pub span: Span,
    /// Per-file scope index of the block's member scope (`u32::MAX` when
    /// unknown: tail resolution from it always misses).
    pub body_scope: u32,
    /// `true` for `declare namespace` (ambient): the export gate lifts.
    pub declared: bool,
    /// Whether the block was exported (gates nested qualification).
    pub exported: bool,
    /// Names directly exported from this block (from the adapter's fact):
    /// resolves the hidden (`TS2694`) vs exported-non-type (declined)
    /// split for members no shape claims.
    pub exported_members: Vec<String>,
}

/// One enum-annotated declaration to check: the [`ConstDecl`] seam plus a
/// hand-fed literal-text seam.
///
/// `init_text` is the source slice of the initializer span (driver-sliced at
/// the adapter's fact span, asserted in tests): numeric spellings parse to
/// membership values, string/boolean spellings render verbatim. `None` for
/// missing, non-literal, and object initializers (those paths never read
/// it) — the same hand-fed seam as M1's `compute` closures and the
/// [`GenericCall`] explicit type arguments.
///
/// `cross_file_deps` carries the declaring file's occurrence nodes a
/// use-file declaration was resolved against (see [`check_one`]): empty on
/// single-file paths, so their memo entries record exactly today's self-dep.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDecl {
    /// The declaration (spans/scopes/shapes as in [`check_file`]).
    pub decl: ConstDecl,
    /// Source slice of the initializer span for literal spellings.
    pub init_text: Option<String>,
    /// Cross-file [`Dep`] edges recorded with this declaration's memo entry.
    pub cross_file_deps: Vec<Dep>,
}

/// One single-file local type alias available for expansion.
/// Driver-mapped from the frontend's `TypeAliasFact` (mechanical name +
/// target-text copy; the binding span stays frontend-side because decline
/// reasons anchor at use sites, never at the alias).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeAliasShape {
    /// Alias name as written (`"Alias"` in `type Alias = Point`).
    pub name: String,
    /// Verbatim aliased-type text (`"Point"`, `"number"`).
    pub target: String,
    /// `true` when the alias declares type parameters (`type Box<T> = …`):
    /// expansion declines instead of instantiating it.
    pub has_type_params: bool,
}

/// Single-file local alias tables for one checking run, bundled so the
/// per-decl helpers stay lean (pedantic arity discipline).
///
/// `aliases` maps from the adapter's alias facts; `const_names` lists every
/// const/let declarator name in the file (built solver-side from the checked
/// declarations) so shadowing checks never depend on binder symbol identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalAliasScope<'a, 'b> {
    /// Local type aliases in source order.
    pub aliases: &'a [TypeAliasShape],
    /// Every const/let declarator name in the file.
    pub const_names: &'b [&'b str],
}

impl LocalAliasScope<'static, 'static> {
    /// Empty scope for paths that thread no alias tables (functions,
    /// narrowing, classes, the legacy interface entry): alias annotations
    /// there keep today's verdicts.
    pub const EMPTY: Self = Self {
        aliases: &[],
        const_names: &[],
    };
}

/// The shape tables one [`check_enums`] run resolves against, bundled so
/// the per-decl helpers stay lean (pedantic arity discipline, mirroring
/// [`GenericCallCtx`]).
#[derive(Clone, Debug, PartialEq)]
pub struct EnumInput<'a> {
    /// Enum shapes driver-mapped from adapter facts.
    pub enums: &'a [EnumShape],
    /// Interface shapes driver-mapped from adapter facts.
    pub interfaces: &'a [InterfaceShape],
    /// Namespace shapes driver-mapped from adapter facts.
    pub namespaces: &'a [NamespaceShape],
}

/// Checks `const`/`let` declarators whose annotations may name interfaces.
///
/// Same [`ConstDecl`] seam as [`check_file`] (spans/scopes from adapter
/// facts, shapes hand-fed until the adapter emits member facts); plus
/// `interfaces`, driver-mapped from the adapter's interface facts (shapes
/// ARE adapter-fed here — only the const side stays hand-fed). Each
/// declaration routes on its annotation text: `{...}`/primitive/union
/// spellings delegate to [`check_one`] unchanged, while any other name
/// resolves scope-sensitively through the [`Binder`] to an
/// [`InterfaceShape`] and runs the shared object comparison with the
/// interface name as the expected spelling. See the module-level interface
/// rules for families, name-spelled elaborations, and declines.
#[must_use]
pub fn check_interfaces(
    file: FileId,
    decls: &[ConstDecl],
    interfaces: &[InterfaceShape],
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    let mut freshness = FreshnessTable::default();
    for (index, decl) in decls.iter().enumerate() {
        if let Some(init) = decl.init_object.as_ref() {
            freshness
                .fresh
                .insert((file, occurrence_node(index)), init.fresh);
        }
    }
    let mut report = FileReport::default();
    for (index, decl) in decls.iter().enumerate() {
        let mut route = InterfaceDeclCtx {
            file,
            node: occurrence_node(index),
            decl,
            interfaces,
            binder,
            db: &mut *db,
            freshness: &freshness,
            report: &mut report,
        };
        route_declaration(&mut route);
    }
    sort_report(&mut report);
    report
}

/// Routing state for one [`check_interfaces`] declaration, bundled so the
/// per-decl helpers stay lean (pedantic arity discipline, mirroring
/// [`GenericCallCtx`]).
struct InterfaceDeclCtx<'a, 'b> {
    file: FileId,
    node: NodeId,
    decl: &'a ConstDecl,
    interfaces: &'b [InterfaceShape],
    binder: &'a Binder,
    db: &'a mut QueryDb,
    freshness: &'a FreshnessTable,
    report: &'a mut FileReport,
}

impl InterfaceDeclCtx<'_, '_> {
    /// Plain spellings (and missing annotations) keep [`check_one`]'s
    /// verdicts by construction.
    fn delegate(&mut self) {
        let mut ctx = CheckCtx {
            file: self.file,
            node: self.node,
            db: &mut *self.db,
            freshness: self.freshness,
            report: &mut *self.report,
            extra: &[],
        };
        // The legacy interface entry threads no alias tables (pinned P038
        // gap: alias annotations there keep today's verdicts).
        check_one(self.decl, self.binder, &mut ctx, &LocalAliasScope::EMPTY);
    }

    /// Resolves an interface-named annotation to its shape: unknown names
    /// diagnose `PITH2304` exactly like [`check_one`]; resolved names no
    /// shape claims decline (non-interface targets — recorded, never
    /// verdict).
    fn resolve_shape(&mut self, span: Span, annotation: &str) {
        let Some(id) = self.binder.resolve(self.file, self.decl.scope, annotation) else {
            self.report.diagnostics.push(PithDiagnostic {
                code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                file: self.file,
                span,
                message: format!("Cannot find name '{annotation}'."),
            });
            return;
        };
        let Some(index) = self
            .interfaces
            .iter()
            .position(|shape| shape.symbol == Some(id))
        else {
            self.report.unsupported.push(UnsupportedDecl {
                file: self.file,
                span,
                reason: format!(
                    "annotation '{annotation}' is not an interface: outside the subset"
                ),
            });
            return;
        };
        let mut tail = CheckCtx {
            file: self.file,
            node: self.node,
            db: &mut *self.db,
            freshness: self.freshness,
            report: &mut *self.report,
            extra: &[],
        };
        check_interface_shape(
            self.decl,
            span,
            annotation,
            &self.interfaces[index],
            &mut tail,
        );
    }
}

/// Routes one declaration: unannotated and plain-spelling annotations
/// delegate; any other name resolves to an interface shape.
fn route_declaration(route: &mut InterfaceDeclCtx<'_, '_>) {
    let decl = route.decl;
    let Some(annotation) = decl.annotation.as_deref().map(str::trim) else {
        route.delegate();
        return;
    };
    if annotation.starts_with('{')
        || annotation.contains('|')
        || annotation_type(annotation).is_some()
        || classify_array_annotation(annotation).is_some()
        || classify_promise_annotation(annotation).is_some()
        || lib_decline_reason(annotation).is_some()
    {
        route.delegate();
        return;
    }
    let span = binder_span(route.binder, route.file, decl);
    route.resolve_shape(span, annotation);
}

/// Gates one resolved interface shape for [`check_interface_shape`]:
/// contradictory facts, heritage, generics, then the first complex member
/// (so reasons stay single). Returns true when a note was pushed and the
/// declaration is done.
fn decline_interface_shape(
    decl: &ConstDecl,
    span: Span,
    shape: &InterfaceShape,
    ctx: &mut CheckCtx<'_>,
) -> bool {
    if decl.init.is_some() && decl.init_object.is_some() {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "contradictory initializer facts: primitive kind with object members"
                .to_owned(),
        });
        return true;
    }
    if decl.init_array.is_some() && (decl.init.is_some() || decl.init_object.is_some()) {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "contradictory initializer facts: array members with \
                another initializer shape"
                .to_owned(),
        });
        return true;
    }
    if !shape.heritage.is_empty() {
        let parents = shape
            .heritage
            .iter()
            .map(|parent| parent.name.as_str())
            .collect::<Vec<&str>>()
            .join(", ");
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: if parents.is_empty() {
                format!(
                    "interface '{}' has a heritage clause: heritage is outside the subset",
                    shape.name
                )
            } else {
                format!(
                    "interface '{}' extends {parents}: heritage is outside the subset",
                    shape.name
                )
            },
        });
        return true;
    }
    if shape.has_type_params {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: format!("generic interface '{}' is outside the subset", shape.name),
        });
        return true;
    }
    if let Some(member) = shape
        .members
        .iter()
        .find(|member| member.complex_reason.is_some())
    {
        let detail = member
            .complex_reason
            .as_deref()
            .unwrap_or("outside the subset");
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: format!(
                "interface '{}': member '{}': {detail}",
                shape.name, member.name
            ),
        });
        return true;
    }
    false
}

/// Checks an array initializer against an interface shape for
/// [`check_interface_shape`]: every REQUIRED member is missing (arrays carry
/// no named members; optional members stay silent — probed P037), spelled
/// the oracle way with the interface name (probed 7.0.2). Unspellable arrays
/// decline instead of mis-spelling.
/// Returns true when the declaration is done.
fn check_interface_array_init(
    decl: &ConstDecl,
    span: Span,
    annotation: &str,
    shape: &InterfaceShape,
    ctx: &mut CheckCtx<'_>,
) -> bool {
    let Some(init_array) = decl.init_array.as_ref() else {
        return false;
    };
    let Some(actual) = spell_array_actual(&init_array.members) else {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "array initializer has no single spellable element type: \
                unions need value facts outside the subset"
                .to_owned(),
        });
        return true;
    };
    let missing: Vec<&str> = shape
        .members
        .iter()
        .filter(|member| !member.optional)
        .map(|member| member.name.as_str())
        .collect();
    emit_missing(
        ctx.file,
        &MissingEmission {
            span,
            expected_text: annotation,
            actual_text: actual,
            missing,
        },
        &mut *ctx.report,
    );
    true
}

/// Gates one resolved interface shape, then runs the shared object
/// comparison with the interface name as the expected spelling.
///
/// Gate order is structural-first (contradictory facts, heritage, generics,
/// complex members — first complex member wins so reasons stay single);
/// member-type classification and literal comparison reuse
/// [`classify_expected`] plus [`finish_object_check`], so verdicts match
/// the `{...}` path by construction. Annotation-less members past the
/// complex gate are unreachable on real paths (the adapter marks them
/// complex) and decline rather than panic.
fn check_interface_shape(
    decl: &ConstDecl,
    span: Span,
    annotation: &str,
    shape: &InterfaceShape,
    ctx: &mut CheckCtx<'_>,
) {
    if decline_interface_shape(decl, span, shape, ctx) {
        return;
    }
    // Array initializers against an interface spell the oracle's missing
    // family with the interface name (probed 7.0.2): every member is
    // missing, since arrays carry no named members.
    if check_interface_array_init(decl, span, annotation, shape, ctx) {
        return;
    }
    let mut parsed = Vec::with_capacity(shape.members.len());
    for member in &shape.members {
        let Some(text) = member.annotation_text.as_deref() else {
            ctx.report.unsupported.push(UnsupportedDecl {
                file: ctx.file,
                span,
                reason: format!(
                    "interface '{}': member '{}' has no comparable annotation: outside the subset",
                    shape.name, member.name
                ),
            });
            return;
        };
        parsed.push(ParsedMember {
            name: member.name.clone(),
            ty: text.to_owned(),
            optional: member.optional,
        });
    }
    let Some(expected) = classify_expected(&parsed, span, ctx) else {
        return;
    };
    finish_object_check(decl, span, &expected, annotation, decl.init, ctx);
}

/// Checks `const`/`let` declarators whose annotations may name enums,
/// interfaces, or namespace-qualified members.
///
/// Same [`ConstDecl`] seam as [`check_file`] (spans/scopes from adapter
/// facts, shapes hand-fed until the adapter emits member facts), plus the
/// hand-fed literal-text seam ([`EnumDecl::init_text`]) and the
/// adapter-fed shape tables ([`EnumInput`]: enums, interfaces, and
/// namespaces driver-mapped from facts with binder identities resolved from
/// the checking [`Binder`]). Each declaration routes on its annotation text:
/// `{...}`/primitive/union spellings delegate to [`check_one`] unchanged,
/// while any other name resolves to a shape — single or
/// namespace-qualified — and runs the enum comparison or the shared object
/// comparison with the short-name spelling. See the module-level enum and
/// namespace rules for families, spellings, and declines.
#[must_use]
pub fn check_enums(
    file: FileId,
    decls: &[EnumDecl],
    input: &EnumInput<'_>,
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    check_enums_with_aliases(file, decls, input, &[], binder, db)
}

/// Checks `const`/`let` declarators with local type aliases in scope,
/// returning the sorted [`FileReport`].
///
/// `aliases` feeds single-level expansion (P038): alias-to-primitive
/// annotations rewrite and check as if written, alias-to-interface/enum
/// annotations relink the underlying shape and check through the existing
/// shape paths spelling the underlying name, and unexpandable targets
/// decline with distinct reasons. [`check_enums`] threads an empty table;
/// [`multifile`] keeps its own import-alias rules and never calls this
/// entry.
#[must_use]
pub fn check_enums_with_aliases(
    file: FileId,
    decls: &[EnumDecl],
    input: &EnumInput<'_>,
    aliases: &[TypeAliasShape],
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    let mut freshness = FreshnessTable::default();
    for (index, decl) in decls.iter().enumerate() {
        if let Some(init) = decl.decl.init_object.as_ref() {
            freshness
                .fresh
                .insert((file, occurrence_node(index)), init.fresh);
        }
    }
    let mut report = FileReport::default();
    let const_names: Vec<&str> = decls.iter().map(|decl| decl.decl.name.as_str()).collect();
    let alias_scope = LocalAliasScope {
        aliases,
        const_names: &const_names,
    };
    for (index, decl) in decls.iter().enumerate() {
        let mut route = EnumDeclCtx {
            file,
            node: occurrence_node(index),
            decl,
            input,
            alias_scope: &alias_scope,
            binder,
            db: &mut *db,
            freshness: &freshness,
            report: &mut report,
        };
        route_enum_declaration(&mut route);
    }
    sort_report(&mut report);
    report
}

/// Routing state for one [`check_enums`] declaration, bundled so the
/// per-decl helpers stay lean (pedantic arity discipline, mirroring
/// [`InterfaceDeclCtx`]).
struct EnumDeclCtx<'a, 'b, 'c> {
    file: FileId,
    node: NodeId,
    decl: &'a EnumDecl,
    input: &'a EnumInput<'b>,
    /// Local alias tables for single-level expansion (P038).
    alias_scope: &'c LocalAliasScope<'b, 'c>,
    binder: &'a Binder,
    db: &'a mut QueryDb,
    freshness: &'a FreshnessTable,
    report: &'a mut FileReport,
}

impl EnumDeclCtx<'_, '_, '_> {
    /// Plain spellings (and missing annotations) keep [`check_one`]'s
    /// verdicts by construction.
    fn delegate(&mut self) {
        let mut ctx = CheckCtx {
            file: self.file,
            node: self.node,
            db: &mut *self.db,
            freshness: self.freshness,
            report: &mut *self.report,
            extra: &self.decl.cross_file_deps,
        };
        check_one(&self.decl.decl, self.binder, &mut ctx, self.alias_scope);
    }

    /// Pushes one [`UnsupportedDecl`] at `span`.
    fn unsupported(&mut self, span: Span, reason: String) {
        self.report.unsupported.push(UnsupportedDecl {
            file: self.file,
            span,
            reason,
        });
    }

    /// Pushes one [`PithDiagnostic`] at `span`.
    fn diagnose(&mut self, span: Span, code: &str, message: String) {
        self.report.diagnostics.push(PithDiagnostic {
            code: code.to_owned(),
            file: self.file,
            span,
            message,
        });
    }

    /// Runs the shared object comparison for a resolved interface shape
    /// with `display` as the expected-type spelling (the short name for
    /// qualified annotations — probed tsc 7.0.2).
    fn check_named_interface(&mut self, span: Span, display: &str, shape: &InterfaceShape) {
        let mut tail = CheckCtx {
            file: self.file,
            node: self.node,
            db: &mut *self.db,
            freshness: self.freshness,
            report: &mut *self.report,
            extra: &self.decl.cross_file_deps,
        };
        check_interface_shape(&self.decl.decl, span, display, shape, &mut tail);
    }

    /// Resolves a single-name annotation: enums check, interfaces run the
    /// shared object path, bare namespaces diagnose `PITH2709`, and
    /// anything else declines (type aliases, classes, values — recorded,
    /// never verdict). Unknown names delegate to [`check_one`], which
    /// diagnoses `PITH2304` exactly like tsc's `TS2304`.
    fn resolve_single(&mut self, span: Span, annotation: &str) {
        let input = self.input;
        let scope = self.decl.decl.scope;
        let Some(id) = self.binder.resolve(self.file, scope, annotation) else {
            self.delegate();
            return;
        };
        let mut found = input.enums.iter().filter(|shape| shape.symbol == Some(id));
        let Some(shape) = found.next() else {
            self.resolve_single_non_enum(span, annotation, id);
            return;
        };
        if found.next().is_some() {
            self.unsupported(
                span,
                format!(
                    "multiple enum declarations for '{annotation}': merging is outside the subset"
                ),
            );
            return;
        }
        self.check_enum_shape(span, annotation, shape);
    }

    /// Single names that resolve past the enum set: interfaces check with
    /// the full name, namespaces diagnose `PITH2709`, local aliases expand
    /// one level (P038), and the rest decline.
    fn resolve_single_non_enum(&mut self, span: Span, annotation: &str, id: SymbolId) {
        let input = self.input;
        if let Some(shape) = input
            .interfaces
            .iter()
            .find(|shape| shape.symbol == Some(id))
        {
            self.check_named_interface(span, annotation, shape);
        } else if input
            .namespaces
            .iter()
            .any(|shape| shape.symbol == Some(id))
        {
            self.diagnose(
                span,
                CODE_NAMESPACE_AS_TYPE,
                format!("Cannot use namespace '{annotation}' as a type."),
            );
        } else {
            self.expand_local_single(span, annotation);
        }
    }

    /// Unclaimed single names (P038): local aliases expand one level —
    /// primitives rewrite and check as if written, interfaces/enums relink
    /// through the existing shape paths spelling the UNDERLYING name (alias
    /// transparency, probed tsc 7.0.2), and unexpandable targets decline.
    /// Anything no alias claims keeps the historical decline.
    fn expand_local_single(&mut self, span: Span, annotation: &str) {
        match expand_local_alias(self.alias_scope, annotation) {
            LocalAliasStep::Keep => {
                self.unsupported(
                    span,
                    format!(
                        "annotation '{annotation}' is not an enum or interface: outside the subset"
                    ),
                );
            }
            LocalAliasStep::Primitive(spelling) => {
                self.check_rewritten_primitive(spelling);
            }
            LocalAliasStep::Shape(target) => {
                self.relink_local_shape(span, annotation, &target);
            }
            LocalAliasStep::Decline(reason) => {
                self.unsupported(span, reason);
            }
        }
    }

    /// Alias-to-primitive: checks as if the target spelling were written,
    /// through [`check_one`] with the file's alias tables.
    fn check_rewritten_primitive(&mut self, spelling: String) {
        let mut rewritten = self.decl.decl.clone();
        rewritten.annotation = Some(spelling);
        let mut ctx = CheckCtx {
            file: self.file,
            node: self.node,
            db: &mut *self.db,
            freshness: self.freshness,
            report: &mut *self.report,
            extra: &self.decl.cross_file_deps,
        };
        check_one(&rewritten, self.binder, &mut ctx, self.alias_scope);
    }

    /// Alias-to-shape: relinks the underlying interface/enum by NAME and
    /// checks through the existing shape paths with the underlying spelling.
    /// Namespace targets diagnose `PITH2709` (tsc reports `TS2709` at the
    /// alias declaration instead — disclosed anchor divergence); names no
    /// shape owns decline instead of verdicting.
    fn relink_local_shape(&mut self, span: Span, annotation: &str, target: &str) {
        let input = self.input;
        match find_local_shape(input, target) {
            LocalShapeHit::Multiple(reason) => {
                self.unsupported(span, reason);
            }
            LocalShapeHit::Interface(shape) => {
                self.check_named_interface(span, target, shape);
            }
            LocalShapeHit::Enum(shape) => {
                self.check_enum_shape(span, target, shape);
            }
            LocalShapeHit::Namespace => {
                self.diagnose(
                    span,
                    CODE_NAMESPACE_AS_TYPE,
                    format!("Cannot use namespace '{target}' as a type."),
                );
            }
            LocalShapeHit::Absent => {
                self.unsupported(
                    span,
                    format!(
                        "type alias '{annotation}' targets '{target}': \
                         no interface, enum, or primitive claims it"
                    ),
                );
            }
        }
    }

    /// Resolves a qualified annotation: namespace heads walk
    /// ([`resolve_ns_tail`]), enum heads collapse member accesses
    /// ([`resolve_enum_head`]), anything else declines. Unresolvable heads
    /// already tracked as unresolved references skip silently (the
    /// [`check_calls`] precedent: tracked once, never double-diagnosed).
    fn resolve_qualified(&mut self, span: Span, annotation: &str) {
        let Some(segments) = split_qualified(annotation) else {
            self.unsupported(
                span,
                format!("qualified annotation '{annotation}' is outside the subset"),
            );
            return;
        };
        let input = self.input;
        let scope = self.decl.decl.scope;
        let Some(head) = self.binder.resolve(self.file, scope, segments[0]) else {
            if !self
                .binder
                .unresolved()
                .iter()
                .any(|entry| entry.file == self.file && entry.name == segments[0])
            {
                self.unsupported(
                    span,
                    format!(
                        "qualified head '{}' resolves to nothing: driver skew",
                        segments[0]
                    ),
                );
            }
            return;
        };
        if input
            .namespaces
            .iter()
            .any(|shape| shape.symbol == Some(head))
        {
            self.resolve_ns_tail(span, annotation, &segments, head);
        } else if input.enums.iter().any(|shape| shape.symbol == Some(head)) {
            self.resolve_enum_head(span, &segments, head);
        } else {
            self.unsupported(
                span,
                format!(
                    "name '{}' is not a namespace: qualified annotations need a namespace head",
                    segments[0]
                ),
            );
        }
    }

    /// Walks `segments[1..]` from namespace `head`: namespaces descend,
    /// enums collapse (member or self), tail interfaces check, exported
    /// non-types decline, and misses diagnose `TS2694` naming the resolved
    /// prefix. A trailing namespace diagnoses `TS2749` on the full path
    /// (probed: the rule is positional — single names get `TS2709`).
    fn resolve_ns_tail(&mut self, span: Span, annotation: &str, segments: &[&str], head: SymbolId) {
        let mut current = head;
        let mut index = 1;
        while index < segments.len() {
            match self.lookup_member(current, segments[index]) {
                MemberLookup::Absent => {
                    self.diagnose(
                        span,
                        CODE_NO_EXPORTED_MEMBER,
                        format!(
                            "Namespace '{}' has no exported member '{}'.",
                            segments[..index].join("."),
                            segments[index]
                        ),
                    );
                    return;
                }
                MemberLookup::Unclaimed => {
                    self.unsupported(
                        span,
                        format!(
                            "member '{}' of '{}' is not an enum or interface: outside the subset",
                            segments[index],
                            segments[..index].join(".")
                        ),
                    );
                    return;
                }
                MemberLookup::Found { id, claimed } => match claimed {
                    Claimed::Namespace => {
                        current = id;
                        index += 1;
                    }
                    Claimed::Enum(enum_index) => {
                        self.resolve_enum_tail(span, segments, index, enum_index);
                        return;
                    }
                    Claimed::Interface(iface_index) => {
                        if index == segments.len() - 1 {
                            let display = segments[index..].join(".");
                            let input = self.input;
                            self.check_named_interface(
                                span,
                                &display,
                                &input.interfaces[iface_index],
                            );
                        } else if index == segments.len() - 2 {
                            // `NS.Point.X` (probed TS2713).
                            let access = segments[index..].join(".");
                            self.diagnose(
                                span,
                                CODE_TYPE_NOT_NAMESPACE,
                                format!(
                                    "Cannot access '{access}' because '{}' is a type, but not a namespace. Did you mean to retrieve the type of the property '{}' in '{}' with '{}[\"{}\"]'?",
                                    segments[index],
                                    segments[index + 1],
                                    segments[index],
                                    segments[index],
                                    segments[index + 1]
                                ),
                            );
                        } else {
                            self.unsupported(
                                span,
                                format!(
                                    "member '{}' is an interface: further qualification is outside the subset",
                                    segments[index]
                                ),
                            );
                        }
                        return;
                    }
                },
            }
        }
        self.diagnose(
            span,
            CODE_VALUE_AS_TYPE,
            format!(
                "'{annotation}' refers to a value, but is being used as a type here. Did you mean 'typeof {annotation}'?"
            ),
        );
    }

    /// Resolves an enum-headed annotation (`Color.Red`, possibly deeper):
    /// the member collapses to its enum (probed tsc 7.0.2); anything else
    /// diagnoses `TS2694` naming the resolved prefix (probed `Color.Nope`).
    fn resolve_enum_head(&mut self, span: Span, segments: &[&str], head: SymbolId) {
        let input = self.input;
        let Some(enum_index) = input
            .enums
            .iter()
            .position(|shape| shape.symbol == Some(head))
        else {
            self.unsupported(
                span,
                format!("enum head '{}' links no shape: driver skew", segments[0]),
            );
            return;
        };
        self.resolve_enum_tail(span, segments, 0, enum_index);
    }

    /// Checks an enum reached at `segments[enum_pos]`: the bare enum and a
    /// trailing member access both check with the namespace-stripped display
    /// (probed: `NS.Dir` spells `Dir`, `NS.Dir.Up` spells `Dir.Up`,
    /// `Color.Red` spells `Color.Red`); misses diagnose `TS2694` on the
    /// resolved prefix (probed `NS.Dir.Nope`, `Color.Nope`).
    fn resolve_enum_tail(
        &mut self,
        span: Span,
        segments: &[&str],
        enum_pos: usize,
        enum_index: usize,
    ) {
        let input = self.input;
        let shape = &input.enums[enum_index];
        if input
            .enums
            .iter()
            .filter(|candidate| candidate.symbol == shape.symbol)
            .count()
            > 1
        {
            self.unsupported(
                span,
                format!(
                    "multiple enum declarations for '{}': merging is outside the subset",
                    shape.name
                ),
            );
            return;
        }
        let member_matched = if enum_pos == segments.len() - 1 {
            let display = segments[enum_pos..].join(".");
            self.check_enum_shape(span, &display, shape);
            return;
        } else {
            shape
                .members
                .iter()
                .any(|member| member.name == segments[enum_pos + 1])
        };
        if member_matched && enum_pos == segments.len() - 2 {
            let display = segments[enum_pos..].join(".");
            self.check_enum_shape(span, &display, shape);
        } else if member_matched {
            self.diagnose(
                span,
                CODE_NO_EXPORTED_MEMBER,
                format!(
                    "Namespace '{}' has no exported member '{}'.",
                    segments[..=enum_pos + 1].join("."),
                    segments[enum_pos + 2]
                ),
            );
        } else {
            self.diagnose(
                span,
                CODE_NO_EXPORTED_MEMBER,
                format!(
                    "Namespace '{}' has no exported member '{}'.",
                    segments[..=enum_pos].join("."),
                    segments[enum_pos + 1]
                ),
            );
        }
    }

    /// Resolves one qualification segment inside namespace `current`.
    ///
    /// Export visibility is facts: claimed members need their own
    /// `exported` flag (lifted when the enclosing namespace is ambient —
    /// probed tsc 7.0.2); unclaimed members consult the enclosing
    /// `exported_members` list, so hidden values diagnose `TS2694` (probed
    /// `NS.Hid`) while exported non-types decline (tsc's `TS2749` is the
    /// pinned divergence — kind is unknowable without value facts). The
    /// scope-membership guard rejects binder walk-up hits outside the block:
    /// they name an outer declaration, not the member.
    fn lookup_member(&self, current: SymbolId, segment: &str) -> MemberLookup {
        let input = self.input;
        let mut unclaimed = false;
        for shape in input
            .namespaces
            .iter()
            .filter(|shape| shape.symbol == Some(current))
        {
            let Some(id) = self.binder.resolve(self.file, shape.body_scope, segment) else {
                continue;
            };
            if !self.member_in_block(current, id) {
                continue;
            }
            let listed = shape.exported_members.iter().any(|name| name == segment);
            match self.claim(id) {
                Some((claimed, exported)) if shape.declared || exported => {
                    return MemberLookup::Found { id, claimed };
                }
                None if shape.declared || listed => {
                    unclaimed = true;
                }
                _ => {}
            }
        }
        if unclaimed {
            MemberLookup::Unclaimed
        } else {
            MemberLookup::Absent
        }
    }

    /// The owning scope of one interned symbol, if any.
    fn symbol_scope(&self, id: SymbolId) -> Option<u32> {
        self.binder.store().get(id).map(|symbol| symbol.scope.index)
    }

    /// Whether `id` names a declaration inside one of `current`'s blocks:
    /// the symbol's owning scope must be a tried body scope, so walk-up
    /// hits from outer scopes never match.
    fn member_in_block(&self, current: SymbolId, id: SymbolId) -> bool {
        let Some(scope) = self.symbol_scope(id) else {
            return false;
        };
        self.input
            .namespaces
            .iter()
            .filter(|shape| shape.symbol == Some(current))
            .any(|shape| shape.body_scope == scope)
    }

    /// Claims a resolved symbol for the first shape holding its identity,
    /// with that shape's own `exported` flag: enums before interfaces
    /// (merged enum+interface pairs are illegal in tsc), namespaces last.
    /// `None` means no shape claims it (values, type aliases, classes).
    fn claim(&self, id: SymbolId) -> Option<(Claimed, bool)> {
        let input = self.input;
        if let Some(index) = input
            .enums
            .iter()
            .position(|shape| shape.symbol == Some(id))
        {
            return Some((Claimed::Enum(index), input.enums[index].exported));
        }
        if let Some(index) = input
            .interfaces
            .iter()
            .position(|shape| shape.symbol == Some(id))
        {
            return Some((Claimed::Interface(index), input.interfaces[index].exported));
        }
        if input
            .namespaces
            .iter()
            .any(|shape| shape.symbol == Some(id))
        {
            let exported = input
                .namespaces
                .iter()
                .filter(|shape| shape.symbol == Some(id))
                .any(|shape| shape.exported);
            return Some((Claimed::Namespace, exported));
        }
        None
    }

    /// Checks one enum-annotated declaration against its shape.
    ///
    /// Gate order is structural-first (contradictory facts, ambient enums,
    /// computed members — the first computed member in source order wins so
    /// reasons stay single), then the initializer shape: objects diagnose
    /// compositionally against the display name, missing and non-literal
    /// initializers decline, and literals check membership (see
    /// [`check_enum_literal`]).
    fn check_enum_shape(&mut self, span: Span, display: &str, shape: &EnumShape) {
        let file = self.file;
        let decl = &self.decl.decl;
        let text = self.decl.init_text.as_deref();
        if decl.init.is_some() && decl.init_object.is_some() {
            self.unsupported(
                span,
                "contradictory initializer facts: primitive kind with object members".to_owned(),
            );
            return;
        }
        if decl.init_array.is_some() && (decl.init.is_some() || decl.init_object.is_some()) {
            self.unsupported(
                span,
                "contradictory initializer facts: array members with \
                another initializer shape"
                    .to_owned(),
            );
            return;
        }
        if shape.declared {
            self.unsupported(
                span,
                format!(
                    "ambient enum '{}' has unknown member values: outside the subset",
                    shape.name
                ),
            );
            return;
        }
        if let Some(member) = shape
            .members
            .iter()
            .find(|member| matches!(&member.value, EnumMemberValue::Computed { .. }))
        {
            let detail = match &member.value {
                EnumMemberValue::Computed { reason } => reason.clone(),
                EnumMemberValue::Number(_) | EnumMemberValue::String(_) => {
                    "outside the subset".to_owned()
                }
            };
            self.unsupported(
                span,
                format!("enum '{}': member '{}': {detail}", shape.name, member.name),
            );
            return;
        }
        if let Some(init_object) = decl.init_object.as_ref() {
            check_primitive_annotation_object_init(file, span, display, init_object, self.report);
            return;
        }
        // Array initializers against an enum spell compositionally
        // (`Type 'number[]' is not assignable to type 'Color'.`); unspellable
        // arrays decline instead of mis-spelling.
        if let Some(init_array) = decl.init_array.as_ref() {
            match spell_array_actual(&init_array.members) {
                Some(actual) => self.diagnose(
                    span,
                    CODE_MISMATCH,
                    format!("Type '{actual}' is not assignable to type '{display}'."),
                ),
                None => self.unsupported(
                    span,
                    "array initializer has no single spellable element type: \
                    unions need value facts outside the subset"
                        .to_owned(),
                ),
            }
            return;
        }
        let Some(init) = decl.init else {
            self.unsupported(
                span,
                "missing initializer: nothing to check against".to_owned(),
            );
            return;
        };
        if init == InitKind::NonLiteral {
            self.unsupported(
                span,
                "non-literal initializer is outside the subset".to_owned(),
            );
            return;
        }
        self.check_enum_literal(span, display, shape, init, text);
    }

    /// Checks one literal initializer against an enum shape: numerics test
    /// membership by value; every other literal diagnoses (probed tsc 7.0.2:
    /// strings never match — even member values — booleans spell
    /// literally, `null`/`undefined` spell widened).
    fn check_enum_literal(
        &mut self,
        span: Span,
        display: &str,
        shape: &EnumShape,
        init: InitKind,
        text: Option<&str>,
    ) {
        match init {
            InitKind::Number => {
                let Some(value) = text.and_then(parse_enum_number) else {
                    self.unsupported(
                        span,
                        match text {
                            Some(found) => format!(
                                "non-decimal numeric literal '{found}' is outside the subset"
                            ),
                            None => "missing literal text for a numeric initializer: driver skew"
                                .to_owned(),
                        },
                    );
                    return;
                };
                // Bitwise equality is exact here: compared values are small
                // integers (parsed literals and auto-incremented member
                // values), exactly representable in f64 with no rounding;
                // hex and non-decimal inits decline before this compare.
                let known = shape.members.iter().any(|member| {
                    matches!(&member.value, EnumMemberValue::Number(found) if found.to_bits() == value.to_bits())
                });
                if !known {
                    self.diagnose(
                        span,
                        CODE_MISMATCH,
                        format!(
                            "Type '{}' is not assignable to type '{display}'.",
                            spell_number(value)
                        ),
                    );
                }
            }
            InitKind::String => {
                let Some(found) = text else {
                    self.unsupported(
                        span,
                        "missing literal text for a string initializer: driver skew".to_owned(),
                    );
                    return;
                };
                self.diagnose(
                    span,
                    CODE_MISMATCH,
                    format!("Type '{found}' is not assignable to type '{display}'."),
                );
            }
            InitKind::Boolean => {
                let spelling = text.unwrap_or("boolean");
                self.diagnose(
                    span,
                    CODE_MISMATCH,
                    format!("Type '{spelling}' is not assignable to type '{display}'."),
                );
            }
            InitKind::Null | InitKind::Undefined | InitKind::Unknown => {
                self.diagnose(
                    span,
                    CODE_MISMATCH,
                    format!(
                        "Type '{}' is not assignable to type '{display}'.",
                        init.name()
                    ),
                );
            }
            InitKind::NonLiteral => {
                self.unsupported(
                    span,
                    "non-literal initializer is outside the subset".to_owned(),
                );
            }
        }
    }
}

/// Routes one declaration: unannotated and plain-spelling annotations
/// delegate to [`check_one`]; any other name resolves single or qualified.
fn route_enum_declaration(route: &mut EnumDeclCtx<'_, '_, '_>) {
    let annotation = route.decl.decl.annotation.as_deref().map(str::trim);
    let Some(annotation) = annotation else {
        route.delegate();
        return;
    };
    if annotation.starts_with('{')
        || annotation.contains('|')
        || annotation_type(annotation).is_some()
        || classify_array_annotation(annotation).is_some()
        || classify_promise_annotation(annotation).is_some()
        || lib_decline_reason(annotation).is_some()
    {
        route.delegate();
        return;
    }
    let span = binder_span(route.binder, route.file, &route.decl.decl);
    if annotation.contains('.') {
        route.resolve_qualified(span, annotation);
        return;
    }
    route.resolve_single(span, annotation);
}

/// One tail-segment lookup inside a namespace: the resolved symbol plus its
/// shape claim when a shape holds its identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MemberLookup {
    /// A shape-claimed, visible member (enum, interface, or namespace).
    Found {
        /// Resolved binder identity.
        id: SymbolId,
        /// Which shape claims it (index into the input tables).
        claimed: Claimed,
    },
    /// Resolved and visible, but no shape claims it (values, type aliases,
    /// classes): the caller declines — kind is unknowable without facts.
    Unclaimed,
    /// Absent, hidden, or outside the block: the caller diagnoses `TS2694`.
    Absent,
}

/// Which shape table claims a resolved member identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Claimed {
    /// An enum shape (index into [`EnumInput::enums`]).
    Enum(usize),
    /// An interface shape (index into [`EnumInput::interfaces`]).
    Interface(usize),
    /// A namespace shape (index unneeded: names come from segments).
    Namespace,
}

/// Splits `NS.Dir` into segments, or `None` for unparseable qualification
/// (empty parts, non-identifier parts): the caller declines, never verdicts.
fn split_qualified(annotation: &str) -> Option<Vec<&str>> {
    let segments: Vec<&str> = annotation.split('.').map(str::trim).collect();
    if segments.len() < 2 {
        return None;
    }
    if segments.iter().any(|segment| !is_name_segment(segment)) {
        return None;
    }
    Some(segments)
}

/// Coarse identifier check (mirrors the union-member name test):
/// alphanumerics plus `_`/`$`, non-empty. Degenerate shapes decline upstream.
fn is_name_segment(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// Parses a plain-decimal numeric literal slice to its value (`1`, `2.5`,
/// `1e2`, `.5` parse via [`str::parse`]; `1_0` parses after tsc's
/// numeric-separator rule is applied); hex/octal/binary and anything else
/// decline — full literal grammars are const-eval the subset refuses
/// (pinned oracle-clean divergences, e.g. `0x0` is clean in tsc).
fn parse_enum_number(text: &str) -> Option<f64> {
    let text = text.trim();
    // tsc separators sit strictly between digits (`_1`, `1_`, `1__0` all
    // error in tsc); Rust's float parser rejects every underscore, so strip
    // only validated ones instead of trusting either side blindly.
    if text.as_bytes().contains(&b'_') {
        let bytes = text.as_bytes();
        for (index, _) in bytes.iter().enumerate().filter(|(_, byte)| **byte == b'_') {
            let left = index.checked_sub(1).and_then(|at| bytes.get(at));
            let right = bytes.get(index + 1);
            if !matches!(left, Some(b'0'..=b'9')) || !matches!(right, Some(b'0'..=b'9')) {
                return None;
            }
        }
        return text.replace('_', "").parse::<f64>().ok();
    }
    text.parse::<f64>().ok()
}

/// Spells a numeric value the way tsc literal types do: Rust's float
/// `Display` already spells integral values bare (`5`, `0`) and fractions
/// shortest round-trip (`2.5`) — exactly tsc's spellings over the probed
/// range (`0x2` against `{ A = 0, B = 1 }` spells `Type '2'`). Exotic
/// magnitudes may diverge textually (documented fold); membership stays
/// exact.
fn spell_number(value: f64) -> String {
    format!("{value}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use pith_symbols::{ScopeInput, SymbolInput, UnresolvedInput};

    const FILE: FileId = FileId(0);

    fn span(lo: u32, hi: u32) -> Span {
        Span { file: FILE, lo, hi }
    }

    fn binder_with(names: &[(&str, Span)]) -> Binder {
        calls_binder(names, &[])
    }

    /// A binder with declared symbols plus unresolved (global) references.
    fn calls_binder(declared: &[(&str, Span)], unresolved: &[&str]) -> Binder {
        let mut binder = Binder::new();
        let symbols: Vec<SymbolInput> = declared
            .iter()
            .map(|(name, decl_span)| SymbolInput {
                scope: 0,
                name: (*name).to_owned(),
                span: *decl_span,
                flags: 0,
            })
            .collect();
        let missing: Vec<UnresolvedInput> = unresolved
            .iter()
            .map(|name| UnresolvedInput {
                name: (*name).to_owned(),
                count: 1,
            })
            .collect();
        binder.build_file(
            FILE,
            &[ScopeInput {
                index: 0,
                parent: u32::MAX,
            }],
            &symbols,
            &missing,
        );
        binder
    }

    fn decl(name: &str, lo: u32, hi: u32, ann: &str, init: InitKind) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some(ann.to_owned()),
            init: Some(init),
            init_object: None,
            init_array: None,
            cast: None,
        }
    }

    fn object_decl(
        name: &str,
        lo: u32,
        hi: u32,
        ann: &str,
        members: Vec<(&str, ObjectMemberKind)>,
    ) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some(ann.to_owned()),
            init: None,
            init_object: Some(ObjectInit {
                members: members
                    .into_iter()
                    .map(|(member, kind)| ObjectMemberInit {
                        name: member.to_owned(),
                        kind,
                    })
                    .collect(),
                fresh: true,
            }),
            init_array: None,
            cast: None,
        }
    }

    /// One interface shape bound to `binder`: the symbol resolves from the
    /// same binder used for checking, mirroring the e2e driver contract.
    fn interface_shape(
        binder: &Binder,
        name: &str,
        scope: u32,
        members: Vec<(&str, &str)>,
    ) -> InterfaceShape {
        InterfaceShape {
            name: name.to_owned(),
            scope,
            symbol: binder.resolve(FILE, scope, name),
            span: span(0, 1),
            members: members
                .into_iter()
                .map(|(member, ty)| InterfaceMember {
                    name: member.to_owned(),
                    annotation_text: Some(ty.to_owned()),
                    optional: false,
                    span: span(0, 1),
                    complex_reason: None,
                })
                .collect(),
            heritage: Vec::new(),
            has_type_params: false,
            exported: false,
        }
    }

    #[test]
    fn interface_correct_is_silent() {
        let binder = binder_with(&[("Point", span(0, 5)), ("v", span(6, 16))]);
        let shapes = [interface_shape(
            &binder,
            "Point",
            0,
            vec![("x", "number"), ("label", "string")],
        )];
        let decls = [object_decl(
            "v",
            6,
            16,
            "Point",
            vec![
                ("x", ObjectMemberKind::Number),
                ("label", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
    }

    #[test]
    fn interface_wrong_member_is_pith2322() {
        let binder = binder_with(&[("Point", span(0, 5)), ("v", span(6, 16))]);
        let shapes = [interface_shape(
            &binder,
            "Point",
            0,
            vec![("x", "number"), ("label", "string")],
        )];
        let decls = [object_decl(
            "v",
            6,
            16,
            "Point",
            vec![
                ("x", ObjectMemberKind::String),
                ("label", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn interface_missing_member_names_interface() {
        let binder = binder_with(&[("User", span(0, 4)), ("v", span(5, 15))]);
        let shapes = [interface_shape(
            &binder,
            "User",
            0,
            vec![("name", "string"), ("age", "number")],
        )];
        let decls = [object_decl(
            "v",
            5,
            15,
            "User",
            vec![("name", ObjectMemberKind::String)],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISSING_MEMBER);
        assert_eq!(
            report.diagnostics[0].message,
            "Property 'age' is missing in type '{ name: string; }' but required in type 'User'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn interface_missing_many_names_interface() {
        let binder = binder_with(&[("Triple", span(0, 6)), ("v", span(7, 17))]);
        let shapes = [interface_shape(
            &binder,
            "Triple",
            0,
            vec![("a", "number"), ("b", "string"), ("c", "boolean")],
        )];
        let decls = [object_decl(
            "v",
            7,
            17,
            "Triple",
            vec![("a", ObjectMemberKind::Number)],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISSING_MANY);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '{ a: number; }' is missing the following properties from type 'Triple': b, c"
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn interface_excess_names_interface() {
        let binder = binder_with(&[("Point", span(0, 5)), ("v", span(6, 16))]);
        let shapes = [interface_shape(&binder, "Point", 0, vec![("x", "number")])];
        let decls = [object_decl(
            "v",
            6,
            16,
            "Point",
            vec![
                ("x", ObjectMemberKind::Number),
                ("extra", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_EXCESS_MEMBER);
        assert_eq!(
            report.diagnostics[0].message,
            concat!(
                "Object literal may only specify known properties, ",
                "and 'extra' does not exist in type 'Point'."
            )
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn interface_unknown_annotation_is_pith2304() {
        let binder = binder_with(&[("v", span(5, 15))]);
        let decls = [object_decl(
            "v",
            5,
            15,
            "Nope",
            vec![("a", ObjectMemberKind::Number)],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &[], &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
        assert_eq!(report.diagnostics[0].span, span(5, 15));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn interface_resolved_non_interface_declines() {
        let binder = binder_with(&[("Alias", span(0, 5)), ("v", span(6, 16))]);
        let decls = [object_decl(
            "v",
            6,
            16,
            "Alias",
            vec![("a", ObjectMemberKind::Number)],
        )];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &[], &binder, &mut db);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("not an interface"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn interface_structural_gates_decline_in_order() {
        let binder = binder_with(&[
            ("H", span(0, 10)),
            ("G", span(11, 21)),
            ("M", span(22, 32)),
            ("h", span(33, 43)),
            ("g", span(44, 54)),
            ("m", span(55, 65)),
        ]);
        let mut heritage = interface_shape(&binder, "H", 0, vec![("a", "number")]);
        heritage.heritage.push(InterfaceHeritage {
            name: "Base".to_owned(),
            span: span(0, 1),
        });
        // Heritage, generics, AND a complex member: heritage wins.
        heritage.has_type_params = true;
        heritage.members.push(InterfaceMember {
            name: "run".to_owned(),
            annotation_text: None,
            optional: false,
            span: span(0, 1),
            complex_reason: Some("method signature 'run' is outside the subset".to_owned()),
        });
        let mut generic = interface_shape(&binder, "G", 0, vec![("a", "number")]);
        generic.has_type_params = true;
        let mut method = interface_shape(&binder, "M", 0, vec![("a", "number")]);
        method.members.push(InterfaceMember {
            name: "run".to_owned(),
            annotation_text: None,
            optional: false,
            span: span(0, 1),
            complex_reason: Some("method signature 'run' is outside the subset".to_owned()),
        });
        let shapes = [heritage, generic, method];
        let decls = [
            object_decl("h", 33, 43, "H", vec![("a", ObjectMemberKind::Number)]),
            object_decl("g", 44, 54, "G", vec![("a", ObjectMemberKind::Number)]),
            object_decl("m", 55, 65, "M", vec![("a", ObjectMemberKind::Number)]),
        ];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 3);
        assert!(
            report.unsupported[0].reason.contains("extends Base"),
            "heritage first: {}",
            report.unsupported[0].reason
        );
        assert!(
            report.unsupported[1].reason.contains("generic interface"),
            "generics second: {}",
            report.unsupported[1].reason
        );
        assert!(
            report.unsupported[2].reason.contains("method signature"),
            "complex member third: {}",
            report.unsupported[2].reason
        );
    }

    #[test]
    fn interface_merged_pair_shares_identity() {
        // Two declarations, one identity: the P005 merge path. The `Foo`
        // declarator's own span is the fallback, but the merged symbol's
        // first-declaration span wins — diagnostics anchor there.
        let first = span(10, 13);
        let mut binder = Binder::new();
        binder.build_file(
            FILE,
            &[ScopeInput {
                index: 0,
                parent: u32::MAX,
            }],
            &[
                SymbolInput {
                    scope: 0,
                    name: "Foo".to_owned(),
                    span: first,
                    flags: 8,
                },
                SymbolInput {
                    scope: 0,
                    name: "Foo".to_owned(),
                    span: span(35, 38),
                    flags: 4,
                },
                SymbolInput {
                    scope: 0,
                    name: "ok".to_owned(),
                    span: span(50, 52),
                    flags: 0,
                },
            ],
            &[],
        );
        let merged = binder.resolve(FILE, 0, "Foo").expect("merged Foo");
        assert_eq!(
            binder
                .store()
                .get(merged)
                .expect("interned")
                .declarations
                .len(),
            2
        );
        let shapes = [InterfaceShape {
            name: "Foo".to_owned(),
            scope: 0,
            symbol: Some(merged),
            span: first,
            members: vec![InterfaceMember {
                name: "a".to_owned(),
                annotation_text: Some("string".to_owned()),
                optional: false,
                span: first,
                complex_reason: None,
            }],
            heritage: Vec::new(),
            has_type_params: false,
            exported: false,
        }];
        let decls = [
            // The merged declarator itself: unannotated, so the verdict is
            // the no-annotation note — anchored at the FIRST declaration.
            ConstDecl {
                name: "Foo".to_owned(),
                span: span(35, 38),
                scope: 0,
                symbol: None,
                kind: DeclKind::Const,
                annotation: None,
                init: Some(InitKind::Number),
                init_object: None,
                init_array: None,
                cast: None,
            },
            // An interface-annotated use resolves through the merged id.
            object_decl("ok", 50, 52, "Foo", vec![("a", ObjectMemberKind::Number)]),
        ];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &shapes, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.unsupported[0].span, first);
    }

    #[test]
    fn interface_plain_spellings_delegate_to_check_one() {
        let binder = binder_with(&[("v", span(0, 10)), ("w", span(11, 21)), ("u", span(22, 32))]);
        let decls = [
            object_decl(
                "v",
                0,
                10,
                "{ a: number }",
                vec![("a", ObjectMemberKind::Number)],
            ),
            decl("w", 11, 21, "number", InitKind::Number),
            decl("u", 22, 32, "number | string", InitKind::Number),
        ];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &[], &binder, &mut db);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("union annotation"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn annotation_type_maps_six_primitives() {
        let cases = [
            ("number", TypeStore::NUMBER),
            ("string", TypeStore::STRING),
            ("boolean", TypeStore::BOOLEAN),
            ("void", TypeStore::VOID),
            ("undefined", TypeStore::UNDEFINED),
            ("null", TypeStore::NULL),
            ("  string  ", TypeStore::STRING),
        ];
        for (text, expected) in cases {
            assert_eq!(annotation_type(text), Some(expected), "annotation {text:?}");
        }
        for unknown in ["Nope", "number[]", "", "Number"] {
            assert_eq!(annotation_type(unknown), None, "annotation {unknown:?}");
        }
    }

    /// One assertion-initialized declaration: the initializer kind is always
    /// `NonLiteral` (assertions classify as expressions), and the cast fact
    /// carries the operand kind plus the verbatim target text.
    fn casted(
        name: &str,
        lo: u32,
        hi: u32,
        ann: Option<&str>,
        operand: InitKind,
        target: &str,
        kind: CastKind,
    ) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: ann.map(str::to_owned),
            init: Some(InitKind::NonLiteral),
            init_object: None,
            init_array: None,
            cast: Some(CastInput {
                operand,
                target: target.to_owned(),
                operand_span: span(lo, hi),
                kind,
            }),
        }
    }

    /// One call site whose single argument is an assertion.
    fn casted_call(operand: InitKind, target: &str, kind: CastKind) -> CallSite {
        CallSite {
            callee: "sn".to_owned(),
            callee_span: span(0, 2),
            span: span(0, 60),
            args: vec![CallArg {
                kind: InitKind::NonLiteral,
                span: span(3, 20),
                cast: Some(CastInput {
                    operand,
                    target: target.to_owned(),
                    operand_span: span(4, 11),
                    kind,
                }),
            }],
        }
    }

    #[test]
    fn boundary_annotations_admit_bearing_values() {
        // Probed tsc 7.0.2: `any` and `unknown` annotations accept every
        // bearing value silently — both directions, every literal.
        let binder = binder_with(&[("m", span(0, 10)), ("u", span(11, 21))]);
        let decls = [
            decl("m", 0, 10, "any", InitKind::Number),
            decl("m", 0, 10, "any", InitKind::String),
            decl("m", 0, 10, "any", InitKind::NonLiteral),
            decl("u", 11, 21, "unknown", InitKind::String),
            decl("u", 11, 21, "unknown", InitKind::Null),
            object_decl("m", 0, 10, "any", vec![("a", ObjectMemberKind::Number)]),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
    }

    #[test]
    fn boundary_annotations_without_init_decline() {
        // Definite assignment stays outside the subset: bearing is required
        // for the boundary silence.
        let binder = binder_with(&[("m", span(0, 10))]);
        let decls = [ConstDecl {
            name: "m".to_owned(),
            span: span(0, 10),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some("any".to_owned()),
            init: None,
            init_object: None,
            init_array: None,
            cast: None,
        }];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("missing initializer"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn never_annotation_diagnoses_bearing_literals() {
        let binder = binder_with(&[("x", span(0, 10)), ("y", span(11, 21))]);
        let decls = [
            decl("x", 0, 10, "never", InitKind::Number),
            decl("y", 11, 21, "never", InitKind::String),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 2);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert!(
                diag.message.ends_with("is not assignable to type 'never'."),
                "message: {}",
                diag.message
            );
        }
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn as_cast_admit_checks_target_through_existing_path() {
        // `(1 as number)` against `number` is clean; against `string` the
        // admitted result diagnoses exactly like a plain literal.
        let binder = binder_with(&[("n", span(0, 10)), ("s", span(11, 21))]);
        let decls = [
            casted(
                "n",
                0,
                10,
                Some("number"),
                InitKind::Number,
                "number",
                CastKind::As,
            ),
            casted(
                "s",
                11,
                21,
                Some("string"),
                InitKind::Number,
                "number",
                CastKind::As,
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn as_cast_decline_reports_both_families() {
        // Probed tsc 7.0.2: `const s: string = ("hello" as number)`
        // reports `TS2322` at the declaration plus `TS2352` at the operand.
        let binder = binder_with(&[("s", span(0, 10))]);
        let decls = [casted(
            "s",
            0,
            10,
            Some("string"),
            InitKind::String,
            "number",
            CastKind::As,
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        // Equal spans (helper reuses the declaration span for the operand)
        // sort stably: the cast diagnostic pushes first.
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_CAST);
        assert_eq!(report.diagnostics[1].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[1].message,
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(
            report.diagnostics[0].message,
            "Conversion of type 'string' to type 'number' may be a mistake \
            because neither type sufficiently overlaps with the other. If \
            this was intentional, convert the expression to 'unknown' first."
        );
        assert_eq!(report.diagnostics[0].span, span(0, 10));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn declined_cast_under_any_keeps_cast_error_only() {
        // Probed tsc 7.0.2: `const m: any = ("hello" as number)` reports
        // `TS2352` alone — the annotation accepts the result.
        let binder = binder_with(&[("m", span(0, 10))]);
        let decls = [casted(
            "m",
            0,
            10,
            Some("any"),
            InitKind::String,
            "number",
            CastKind::As,
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_CAST);
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn unknown_result_diagnoses_against_primitives() {
        // Probed tsc 7.0.2: `const n: number = ("x" as unknown)` reports a
        // lone `TS2322` spelling `unknown` — no cast diagnostic.
        let binder = binder_with(&[("n", span(0, 10))]);
        let decls = [casted(
            "n",
            0,
            10,
            Some("number"),
            InitKind::String,
            "unknown",
            CastKind::As,
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'number'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn satisfies_admits_transparently_to_operand() {
        // `satisfies` checks the operand type downstream, not the target:
        // `(1 satisfies number)` against `string` reports the operand.
        let binder = binder_with(&[("t", span(0, 10)), ("s", span(11, 21))]);
        let decls = [
            casted(
                "t",
                0,
                10,
                Some("string"),
                InitKind::String,
                "string",
                CastKind::Satisfies,
            ),
            casted(
                "s",
                11,
                21,
                Some("string"),
                InitKind::Number,
                "number",
                CastKind::Satisfies,
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' is not assignable to type 'string'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn satisfies_decline_spells_ts1360() {
        // `("x" satisfies number)` against `boolean`: `TS1360` at the
        // operand plus the downstream operand-vs-annotation `TS2322`.
        let binder = binder_with(&[("b", span(0, 10))]);
        let decls = [casted(
            "b",
            0,
            10,
            Some("boolean"),
            InitKind::String,
            "number",
            CastKind::Satisfies,
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_SATISFIES);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' does not satisfy the expected type 'number'."
        );
        assert_eq!(report.diagnostics[1].code, CODE_MISMATCH);
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn angle_assertion_shares_as_rule() {
        let binder = binder_with(&[("t", span(0, 10))]);
        let decls = [casted(
            "t",
            0,
            10,
            Some("number"),
            InitKind::Number,
            "string",
            CastKind::Angle,
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_CAST);
        assert_eq!(report.diagnostics[1].code, CODE_MISMATCH);
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn complex_casts_decline_with_reasons() {
        // Non-literal operands, object targets, and unsliceable targets
        // decline the whole declaration — never a forced verdict.
        let binder = binder_with(&[("a", span(0, 10)), ("b", span(11, 21)), ("c", span(22, 32))]);
        let decls = [
            casted(
                "a",
                0,
                10,
                Some("number"),
                InitKind::NonLiteral,
                "number",
                CastKind::As,
            ),
            casted(
                "b",
                11,
                21,
                Some("number"),
                InitKind::String,
                "{ a: number }",
                CastKind::As,
            ),
            casted(
                "c",
                22,
                32,
                Some("number"),
                InitKind::String,
                "",
                CastKind::As,
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 3);
        assert!(
            report.unsupported[0].reason.contains("operand"),
            "reason: {}",
            report.unsupported[0].reason
        );
        assert!(
            report.unsupported[1].reason.contains("target"),
            "reason: {}",
            report.unsupported[1].reason
        );
        assert!(
            report.unsupported[2].reason.contains("target"),
            "reason: {}",
            report.unsupported[2].reason
        );
    }

    #[test]
    fn unannotated_declined_cast_still_diagnoses() {
        // Probed tsc 7.0.2: `const s = "hello" as number` spells `TS2352`
        // with no annotation to check against.
        let binder = binder_with(&[("s", span(0, 10)), ("t", span(11, 21))]);
        let decls = [
            casted("s", 0, 10, None, InitKind::String, "number", CastKind::As),
            casted("t", 11, 21, None, InitKind::Number, "number", CastKind::As),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_CAST);
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("no annotation"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn any_and_unknown_params_accept_every_literal() {
        // Probed tsc 7.0.2: `takeAny("oops")` and `h("s")` against
        // `unknown` are clean; the mixed declaration still checks the
        // non-boundary position.
        let binder = Binder::new();
        let take_any = callable("takeAny", vec![("x", "any")]);
        let take_unknown = callable("takeUnknown", vec![("x", "unknown")]);
        let mixed = callable("mixed", vec![("x", "any"), ("y", "number")]);
        let decls = [take_any, take_unknown, mixed];
        let clean = [
            call("takeAny", span(0, 7), vec![(InitKind::String, span(8, 14))]),
            call(
                "takeUnknown",
                span(0, 11),
                vec![(InitKind::Number, span(12, 13))],
            ),
            call(
                "mixed",
                span(0, 5),
                vec![
                    (InitKind::String, span(6, 10)),
                    (InitKind::Number, span(12, 13)),
                ],
            ),
        ];
        let report = check_calls(FILE, &decls, &clean, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(report.unsupported.is_empty());
        let wrong = [call(
            "mixed",
            span(0, 5),
            vec![
                (InitKind::String, span(6, 10)),
                (InitKind::String, span(12, 18)),
            ],
        )];
        let report = check_calls(FILE, &decls, &wrong, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn never_param_declines() {
        // Unprobed message shape: never forced, always recorded.
        let binder = Binder::new();
        let decls = [callable("takeNever", vec![("x", "never")])];
        let calls = [call(
            "takeNever",
            span(0, 9),
            vec![(InitKind::Number, span(10, 11))],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("never"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn declined_cast_argument_reports_both_families() {
        // Probed tsc 7.0.2: `sn(("hello" as number))` against `(x: string)`
        // reports `TS2345` plus `TS2352`.
        let binder = Binder::new();
        let decls = [callable("sn", vec![("x", "string")])];
        let calls = [casted_call(InitKind::String, "number", CastKind::As)];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        // Sorted by span: the paren-inclusive argument span precedes the
        // inner operand span, so the arg-type verdict orders first.
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        assert_eq!(report.diagnostics[1].code, CODE_CAST);
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn correct_subset_is_silent_and_memoized() {
        let binder = binder_with(&[("a", span(0, 10)), ("b", span(11, 21)), ("c", span(22, 32))]);
        let decls = [
            decl("a", 0, 10, "number", InitKind::Number),
            decl("b", 11, 21, "string", InitKind::String),
            decl("c", 22, 32, "boolean", InitKind::Boolean),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(db.recompute_count(), 3);
        // A second pass over the same declarations must hit the memo cache.
        let repeat = check_file(FILE, &decls, &binder, &mut db);
        assert!(repeat.diagnostics.is_empty());
        assert_eq!(db.recompute_count(), 3);
    }

    #[test]
    fn literal_mismatches_are_sorted_pith2322() {
        let binder = binder_with(&[("a", span(40, 50)), ("b", span(0, 10)), ("c", span(20, 30))]);
        // Caller order is scrambled; diagnostics must come out sorted by lo.
        let decls = [
            decl("a", 40, 50, "number", InitKind::String),
            decl("b", 0, 10, "string", InitKind::Number),
            decl("c", 20, 30, "boolean", InitKind::Number),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        let codes: Vec<&str> = report.diagnostics.iter().map(|d| d.code.as_str()).collect();
        assert_eq!(codes, [CODE_MISMATCH, CODE_MISMATCH, CODE_MISMATCH]);
        let los: Vec<u32> = report.diagnostics.iter().map(|d| d.span.lo).collect();
        assert_eq!(los, [0, 20, 40]);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' is not assignable to type 'string'."
        );
    }

    #[test]
    fn unknown_annotation_is_pith2304() {
        let binder = binder_with(&[("v", span(5, 15))]);
        let decls = [decl("v", 5, 15, "Nope", InitKind::Number)];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
        assert_eq!(report.diagnostics[0].span, span(5, 15));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn out_of_subset_is_unsupported_never_silent() {
        let binder = binder_with(&[
            ("u", span(0, 8)),
            ("n", span(9, 17)),
            ("e", span(18, 26)),
            ("m", span(27, 35)),
        ]);
        let decls = [
            decl("u", 0, 8, "number | string", InitKind::Number),
            ConstDecl {
                name: "n".to_owned(),
                span: span(9, 17),
                scope: 0,
                symbol: None,
                kind: DeclKind::Const,
                annotation: None,
                init: Some(InitKind::Number),
                init_object: None,
                init_array: None,
                cast: None,
            },
            decl("e", 18, 26, "number", InitKind::NonLiteral),
            ConstDecl {
                name: "m".to_owned(),
                span: span(27, 35),
                scope: 0,
                symbol: None,
                kind: DeclKind::Const,
                annotation: Some("number".to_owned()),
                init: None,
                init_object: None,
                init_array: None,
                cast: None,
            },
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 4);
        let los: Vec<u32> = report.unsupported.iter().map(|u| u.span.lo).collect();
        assert_eq!(los, [0, 9, 18, 27]);
    }

    #[test]
    fn multi_declarator_mixed_verdicts() {
        let binder = binder_with(&[
            ("first", span(0, 12)),
            ("second", span(13, 27)),
            ("third", span(28, 42)),
        ]);
        let decls = [
            decl("first", 0, 12, "number", InitKind::Number),
            decl("second", 13, 27, "string", InitKind::String),
            decl("third", 28, 42, "boolean", InitKind::Number),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(28, 42));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn binder_span_wins_over_caller_fallback() {
        let binder = binder_with(&[("v", span(100, 110))]);
        // Caller span is a stale fallback; the verdict must point at the
        // real declaration span from the binder.
        let decls = [decl("v", 0, 5, "number", InitKind::String)];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(100, 110));
    }

    #[test]
    fn unbound_name_falls_back_to_caller_span() {
        let binder = binder_with(&[]);
        let decls = [decl("ghost", 7, 17, "string", InitKind::Number)];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(7, 17));
    }

    fn shadowing_binder() -> (Binder, Span, Span) {
        let outer = span(0, 10);
        let inner = span(50, 60);
        let mut binder = Binder::new();
        binder.build_file(
            FILE,
            &[
                ScopeInput {
                    index: 0,
                    parent: u32::MAX,
                },
                ScopeInput {
                    index: 1,
                    parent: 0,
                },
            ],
            &[
                SymbolInput {
                    scope: 0,
                    name: "x".to_owned(),
                    span: outer,
                    flags: 0,
                },
                SymbolInput {
                    scope: 1,
                    name: "x".to_owned(),
                    span: inner,
                    flags: 0,
                },
            ],
            &[],
        );
        (binder, outer, inner)
    }

    fn scoped_decl(name: &str, fallback: Span, scope: u32, ann: &str, init: InitKind) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: fallback,
            scope,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some(ann.to_owned()),
            init: Some(init),
            init_object: None,
            init_array: None,
            cast: None,
        }
    }

    #[test]
    fn shadowed_same_name_verdicts_against_own_scopes() {
        // The outer `x` is fine; the inner `x` shadows it and mismatches.
        // The old name-only span lookup pointed every same-name verdict at
        // the FIRST declaration (the outer span); scope-sensitive
        // resolution must point the inner verdict at the inner span.
        let (binder, outer, inner) = shadowing_binder();
        let decls = [
            scoped_decl("x", outer, 0, "string", InitKind::String),
            scoped_decl("x", inner, 1, "number", InitKind::String),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, inner);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn exact_symbol_identity_beats_scope_lookup() {
        // A driver-resolved SymbolId pins the span even when the name and
        // scope would resolve elsewhere (or nowhere).
        let (binder, _outer, inner) = shadowing_binder();
        let id = binder.resolve(FILE, 1, "x").expect("inner x resolves");
        let decl = ConstDecl {
            name: "renamed".to_owned(),
            span: span(999, 1005),
            scope: u32::MAX,
            symbol: Some(id),
            kind: DeclKind::Const,
            annotation: Some("number".to_owned()),
            init: Some(InitKind::String),
            init_object: None,
            init_array: None,
            cast: None,
        };
        let mut db = QueryDb::new();
        let report = check_file(FILE, &[decl], &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, inner);
    }

    #[test]
    fn foreign_symbol_identity_is_ignored() {
        // An out-of-range SymbolId resolves to nothing: the scope lookup
        // misses too ("ghost" is unbound), so the caller fallback wins.
        // (A foreign in-range id is indistinguishable from a local one with
        // bare ids — callers must only pass same-binder ids per the
        // `binder_span` contract; see `cross_file_identity_is_ignored` for
        // the file-guard path.)
        let (binder, _outer, _inner) = shadowing_binder();
        let decl = ConstDecl {
            name: "ghost".to_owned(),
            span: span(7, 17),
            scope: 0,
            symbol: Some(SymbolId(u32::MAX)),
            kind: DeclKind::Const,
            annotation: Some("string".to_owned()),
            init: Some(InitKind::Number),
            init_object: None,
            init_array: None,
            cast: None,
        };
        let mut db = QueryDb::new();
        let report = check_file(FILE, &[decl], &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(7, 17));
    }

    #[test]
    fn cross_file_identity_is_ignored() {
        // A valid local id queried under another file trips the file guard:
        // the scope lookup misses (no tree for that file), so the caller
        // fallback wins instead of laundering the local span in.
        let (binder, _outer, _inner) = shadowing_binder();
        let id = binder.resolve(FILE, 0, "x").expect("outer x resolves");
        let decl = ConstDecl {
            name: "x".to_owned(),
            span: span(7, 17),
            scope: 0,
            symbol: Some(id),
            kind: DeclKind::Const,
            annotation: Some("string".to_owned()),
            init: Some(InitKind::Number),
            init_object: None,
            init_array: None,
            cast: None,
        };
        let mut db = QueryDb::new();
        let other = FileId(41);
        let report = check_file(other, &[decl], &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(7, 17));
    }

    #[test]
    fn let_declarator_checks_like_const() {
        // `let` uses the same rules (mutability unchecked): a match is
        // silent, a mismatch diagnoses identically to `const`.
        let binder = binder_with(&[("a", span(0, 10)), ("b", span(11, 21))]);
        let decls = [
            ConstDecl {
                kind: DeclKind::Let,
                cast: None,
                ..decl("a", 0, 10, "number", InitKind::Number)
            },
            ConstDecl {
                kind: DeclKind::Let,
                cast: None,
                ..decl("b", 11, 21, "number", InitKind::String)
            },
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(11, 21));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn object_correct_is_silent_and_memoized() {
        let binder = binder_with(&[("p", span(0, 10))]);
        let decls = [object_decl(
            "p",
            0,
            10,
            "{ x: number; label: string }",
            vec![
                ("x", ObjectMemberKind::Number),
                ("label", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(db.recompute_count(), 1);
        let repeat = check_file(FILE, &decls, &binder, &mut db);
        assert!(repeat.diagnostics.is_empty());
        assert_eq!(db.recompute_count(), 1);
    }

    #[test]
    fn object_wrong_member_is_pith2322() {
        let binder = binder_with(&[("p", span(0, 10))]);
        let decls = [object_decl(
            "p",
            0,
            10,
            "{ x: number; label: string }",
            vec![
                ("x", ObjectMemberKind::String),
                ("label", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(0, 10));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn object_missing_member_is_pith2741() {
        let binder = binder_with(&[("u", span(0, 10))]);
        let decls = [object_decl(
            "u",
            0,
            10,
            "{ name: string; age: number }",
            vec![("name", ObjectMemberKind::String)],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISSING_MEMBER);
        assert_eq!(
            report.diagnostics[0].message,
            "Property 'age' is missing in type '{ name: string; }' but required in type '{ name: string; age: number; }'."
        );
    }

    #[test]
    fn object_optional_members_absent_silent_present_checked() {
        // Probed tsc 7.0.2 P037: absent optional members stay silent,
        // present ones check exactly like required members, and missing
        // calculations skip them (only `x` is ever reported).
        let binder = binder_with(&[
            ("a", span(0, 10)),
            ("b", span(11, 21)),
            ("c", span(22, 32)),
            ("d", span(33, 43)),
        ]);
        let ann = "{ x: number; y?: number }";
        let decls = [
            object_decl("a", 0, 10, ann, vec![("x", ObjectMemberKind::Number)]),
            object_decl(
                "b",
                11,
                21,
                ann,
                vec![
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::Number),
                ],
            ),
            object_decl(
                "c",
                22,
                32,
                ann,
                vec![
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::String),
                ],
            ),
            object_decl("d", 33, 43, ann, Vec::new()),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(22, 32));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(report.diagnostics[1].code, CODE_MISSING_MEMBER);
        assert_eq!(report.diagnostics[1].span, span(33, 43));
        assert_eq!(
            report.diagnostics[1].message,
            "Property 'x' is missing in type '{}' but required in type \
            '{ x: number; y?: number | undefined; }'."
        );
    }

    #[test]
    fn interface_optional_member_absent_silent_present_wrong() {
        // Same rule through the interface path (the expected spelling stays
        // the interface name): absent silent, present-wrong `TS2322`.
        let binder = binder_with(&[("P", span(0, 5)), ("a", span(6, 16)), ("b", span(17, 27))]);
        let mut shape = interface_shape(&binder, "P", 0, vec![("x", "number"), ("y", "number")]);
        shape.members[1].optional = true;
        let decls = [
            object_decl("a", 6, 16, "P", vec![("x", ObjectMemberKind::Number)]),
            object_decl(
                "b",
                17,
                27,
                "P",
                vec![
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::String),
                ],
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_interfaces(FILE, &decls, &[shape], &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(17, 27));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn object_missing_many_is_pith2739() {
        // The actual type keeps literal order (`secure` first) and fresh
        // booleans spell literally (`false`); the missing list keeps
        // annotation order (`port, retries`).
        let binder = binder_with(&[("c", span(0, 10))]);
        let decls = [object_decl(
            "c",
            0,
            10,
            "{ host: string; port: number; secure: boolean; retries: number }",
            vec![
                ("secure", ObjectMemberKind::Boolean(false)),
                ("host", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISSING_MANY);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '{ secure: false; host: string; }' is missing the following properties from type '{ host: string; port: number; secure: boolean; retries: number; }': port, retries"
        );
    }

    #[test]
    fn object_excess_is_pith2353_when_fresh() {
        let binder = binder_with(&[("p", span(0, 10))]);
        let decls = [object_decl(
            "p",
            0,
            10,
            "{ x: number }",
            vec![
                ("x", ObjectMemberKind::Number),
                ("extra", ObjectMemberKind::String),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_EXCESS_MEMBER);
        assert_eq!(
            report.diagnostics[0].message,
            "Object literal may only specify known properties, and 'extra' does not exist in type '{ x: number; }'."
        );
    }

    #[test]
    fn object_stale_excess_is_unsupported_never_diagnosed() {
        // The freshness gate: a stale (aliased) literal with an excess
        // candidate must not diagnose — freshness lives per-occurrence, and
        // only fresh occurrences may fire `TS2353`.
        let binder = binder_with(&[("p", span(0, 10))]);
        let mut stale = object_decl(
            "p",
            0,
            10,
            "{ x: number }",
            vec![
                ("x", ObjectMemberKind::Number),
                ("extra", ObjectMemberKind::String),
            ],
        );
        stale.init_object.as_mut().expect("object init").fresh = false;
        let mut db = QueryDb::new();
        let report = check_file(FILE, &[stale], &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("fresh"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn object_wrong_beats_excess_and_missing() {
        // tsc priority (probed 7.0.2): any wrong member suppresses excess
        // and missing diagnostics on the same declaration.
        let binder = binder_with(&[("p", span(0, 10))]);
        let decls = [object_decl(
            "p",
            0,
            10,
            "{ x: number; y: string }",
            vec![
                ("x", ObjectMemberKind::String),
                ("extra", ObjectMemberKind::Number),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn object_excess_beats_missing() {
        // tsc priority (probed 7.0.2): excess suppresses missing on the
        // same declaration.
        let binder = binder_with(&[("p", span(0, 10))]);
        let decls = [object_decl(
            "p",
            0,
            10,
            "{ x: number; y: string }",
            vec![
                ("x", ObjectMemberKind::Number),
                ("extra", ObjectMemberKind::Number),
            ],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_EXCESS_MEMBER);
        assert_eq!(
            report.diagnostics[0].message,
            "Object literal may only specify known properties, and 'extra' does not exist in type '{ x: number; y: string; }'."
        );
    }

    #[test]
    fn object_out_of_subset_shapes_are_unsupported() {
        let binder = binder_with(&[
            ("u", span(0, 8)),
            ("n", span(9, 17)),
            ("e", span(18, 26)),
            ("q", span(27, 35)),
        ]);
        let union = object_decl(
            "u",
            0,
            8,
            "{ a: number | string }",
            vec![("a", ObjectMemberKind::Number)],
        );
        let nested = object_decl(
            "n",
            9,
            17,
            "{ inner: { x: number } }",
            vec![("inner", ObjectMemberKind::NonLiteral)],
        );
        let non_literal_member = object_decl(
            "e",
            18,
            26,
            "{ a: number }",
            vec![("a", ObjectMemberKind::NonLiteral)],
        );
        let empty = object_decl("q", 27, 35, "{}", vec![("a", ObjectMemberKind::Number)]);
        // NOTE (P037): `{ a?: number }` used to sit here as the fifth
        // decline, but optional members are now admitted (absent silent,
        // present checked) with their own differential cover — keeping it
        // would assert the old verdict against the new subset.
        let decls = [union, nested, non_literal_member, empty];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 4);
    }

    #[test]
    fn object_unknown_member_type_is_pith2304() {
        let binder = binder_with(&[("u", span(0, 10))]);
        let decls = [object_decl(
            "u",
            0,
            10,
            "{ a: Nope }",
            vec![("a", ObjectMemberKind::Number)],
        )];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
    }

    #[test]
    fn cross_shape_mismatches_are_pith2322() {
        // Oracle spells cross-shapes compositionally (probed 7.0.2):
        // primitive annotation with an object init, and object annotation
        // with a primitive init.
        let binder = binder_with(&[("x", span(0, 10)), ("y", span(11, 21))]);
        let object_init = object_decl("x", 0, 10, "number", vec![("a", ObjectMemberKind::Number)]);
        let primitive_init = ConstDecl {
            name: "y".to_owned(),
            span: span(11, 21),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some("{ a: number }".to_owned()),
            init: Some(InitKind::Number),
            init_object: None,
            init_array: None,
            cast: None,
        };
        let mut db = QueryDb::new();
        let report = check_file(FILE, &[object_init, primitive_init], &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '{ a: number; }' is not assignable to type 'number'."
        );
        assert_eq!(report.diagnostics[0].span, span(0, 10));
        assert_eq!(report.diagnostics[1].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[1].message,
            "Type 'number' is not assignable to type '{ a: number; }'."
        );
        assert_eq!(report.diagnostics[1].span, span(11, 21));
    }

    #[test]
    fn parse_object_annotation_covers_separators() {
        let parsed = parse_object_annotation("{ a: number; b: string, c: boolean\n d: null }")
            .expect("parses");
        let names: Vec<&str> = parsed.iter().map(|member| member.name.as_str()).collect();
        assert_eq!(names, ["a", "b", "c", "d"]);
        assert!(parsed.iter().all(|member| !member.optional));
        assert_eq!(
            parse_object_annotation("{ a: number; }")
                .expect("parses")
                .len(),
            1
        );
        assert!(parse_object_annotation("{}").expect("parses").is_empty());
        let opt = parse_object_annotation("{ a: number; b?: string }").expect("parses");
        assert_eq!(opt.len(), 2);
        assert!(!opt[0].optional);
        assert!(opt[1].optional);
        assert_eq!(opt[1].name, "b");
        assert_eq!(opt[1].ty, "string");
        for bad in [
            "number",
            "{ a }",
            "{ 'a': number }",
            "{ : number }",
            "{ a: }",
        ] {
            assert!(
                parse_object_annotation(bad).is_none(),
                "must not parse: {bad:?}"
            );
        }
    }

    #[test]
    fn contradictory_initializer_pair_is_unsupported() {
        // A driver bug (primitive kind AND object members) must be
        // recorded, never resolved by silently ignoring one side.
        let binder = binder_with(&[("p", span(0, 10))]);
        let mut both = object_decl(
            "p",
            0,
            10,
            "{ a: number }",
            vec![("a", ObjectMemberKind::Number)],
        );
        both.init = Some(InitKind::Number);
        let mut db = QueryDb::new();
        let report = check_file(FILE, &[both], &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("contradictory"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    /// One array-literal declaration for lib tests.
    fn array_decl(
        name: &str,
        lo: u32,
        hi: u32,
        ann: &str,
        members: Vec<ArrayMemberKind>,
    ) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some(ann.to_owned()),
            init: None,
            init_object: None,
            init_array: Some(ArrayInit { members }),
            cast: None,
        }
    }

    #[test]
    fn array_annotation_classifier_admits_single_primitive_elements() {
        for (text, spelling) in [
            ("Array<number>", "number"),
            ("number[]", "number"),
            ("Array<string>", "string"),
            ("boolean[]", "boolean"),
            ("Array<null>", "null"),
            ("undefined[]", "undefined"),
            ("Array<any>", "any"),
            ("Array<unknown>", "unknown"),
            ("Array<never>", "never"),
            ("Array <number>", "number"),
        ] {
            match classify_array_annotation(text) {
                Some(ArrayAnnotation::Admit(element)) => {
                    assert_eq!(element.spelling, spelling, "spelling for {text:?}");
                }
                other => panic!("must admit {text:?}: {other:?}"),
            }
        }
        for bad in [
            "Array",
            "Array<>",
            "Array<number, string>",
            "Array<number | string>",
            "Array<Array<number>>",
            "Array<Promise<number>>",
            "Array<void>",
            "Array<{ x: number }>",
            "readonly number[]",
        ] {
            match classify_array_annotation(bad) {
                Some(ArrayAnnotation::Decline(_)) => {}
                other => panic!("must decline {bad:?}: {other:?}"),
            }
        }
        for plain in [
            "number",
            "Record<string, number>",
            "number | string",
            // Union spellings are not array spellings even when a member
            // is one: `None` routes them to union handling, which declines
            // shaped members there instead of mis-attributing the verdict.
            "number[] | string",
        ] {
            assert!(
                classify_array_annotation(plain).is_none(),
                "not an array spelling: {plain:?}"
            );
        }
    }

    #[test]
    fn promise_annotation_classifier_admits_checkable_payloads() {
        match classify_promise_annotation("Promise<number>") {
            Some(PromiseAnnotation::Admit(PromiseInner::Element(element))) => {
                assert_eq!(element.spelling, "number");
            }
            other => panic!("must admit payload: {other:?}"),
        }
        match classify_promise_annotation("Promise<Array<number>>") {
            Some(PromiseAnnotation::Admit(PromiseInner::Array(element))) => {
                assert_eq!(element.spelling, "number");
            }
            other => panic!("must admit array payload: {other:?}"),
        }
        match classify_promise_annotation("Promise<unknown>") {
            Some(PromiseAnnotation::Admit(PromiseInner::Element(element))) => {
                assert_eq!(element.spelling, "unknown");
            }
            other => panic!("must admit unknown payload: {other:?}"),
        }
        for bad in [
            "Promise<>",
            "Promise<number, string>",
            "Promise<number | string>",
            "Promise<never>",
            "Promise<void>",
            "Promise<Promise<number>>",
            "Promise<{ x: number }>",
            "Promise<Record<string, number>>",
        ] {
            match classify_promise_annotation(bad) {
                Some(PromiseAnnotation::Decline(_)) => {}
                other => panic!("must decline {bad:?}: {other:?}"),
            }
        }
        for plain in ["Promise", "number", "Array<number>"] {
            assert!(
                classify_promise_annotation(plain).is_none(),
                "not a promise spelling: {plain:?}"
            );
        }
    }

    #[test]
    fn lib_decline_reason_names_families() {
        for (text, family) in [
            ("[number, string]", "tuple"),
            ("Record<string, number>", "utility"),
            ("Partial<{ x: number }>", "utility"),
            ("Iterable<number>", "iterable"),
            ("Map<string, number>", "collection"),
            ("Set<number>", "collection"),
            ("Int32Array", "typed-array"),
            ("Window", "DOM"),
            ("Array", "generic"),
            ("Promise", "generic"),
            ("ReadonlyArray<number>", "readonly"),
        ] {
            let reason =
                lib_decline_reason(text).unwrap_or_else(|| panic!("must decline {text:?}"));
            assert!(reason.contains(family), "reason for {text:?}: {reason}");
        }
        for plain in ["number", "Nope", "{ a: number }", "NS.Point"] {
            assert!(
                lib_decline_reason(plain).is_none(),
                "not lib-shaped: {plain:?}"
            );
        }
    }

    #[test]
    fn array_members_diagnose_per_member_and_skip_non_literals() {
        // Wrong members diagnose one `TS2322` each in literal order;
        // non-literal members skip silently (probed tsc 7.0.2).
        let binder = binder_with(&[("a", span(0, 10)), ("b", span(11, 21))]);
        let decls = [
            array_decl(
                "a",
                0,
                10,
                "Array<number>",
                vec![
                    ArrayMemberKind::String,
                    ArrayMemberKind::NonLiteral,
                    ArrayMemberKind::Boolean,
                ],
            ),
            array_decl("b", 11, 21, "string[]", vec![ArrayMemberKind::Number]),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 3);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(report.diagnostics[0].span, span(0, 10));
        assert_eq!(
            report.diagnostics[1].message,
            "Type 'boolean' is not assignable to type 'number'."
        );
        assert_eq!(
            report.diagnostics[2].message,
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(report.diagnostics[2].span, span(11, 21));
    }

    #[test]
    fn promise_returns_unwrap_only_for_async_functions() {
        // The non-async declaration declines (tsc's `TS2322`/`TS2739`
        // shapes are unspellable); the async one unwraps and diagnoses.
        let binder = binder_with(&[("f", span(0, 10)), ("g", span(11, 21))]);
        let sync = function(
            "f",
            0,
            10,
            vec![],
            Some("Promise<number>"),
            single(InitKind::Number),
        );
        let mut asynk = function(
            "g",
            11,
            21,
            vec![],
            Some("Promise<number>"),
            single(InitKind::String),
        );
        asynk.is_async = true;
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &[sync, asynk], &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(report.diagnostics[0].span, span(11, 21));
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("non-async"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    fn function(
        name: &str,
        lo: u32,
        hi: u32,
        params: Vec<(&str, bool)>,
        annotation: Option<&str>,
        body: FunctionBody,
    ) -> FunctionDecl {
        FunctionDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            params: params
                .into_iter()
                .map(|(name, annotated)| FunctionParam {
                    name: name.to_owned(),
                    annotated,
                    annotation: None,
                    optional: false,
                    is_rest: false,
                })
                .collect(),
            params_complex: false,
            is_async: false,
            has_type_params: false,
            return_annotation: annotation.map(str::to_owned),
            body,
        }
    }

    fn single(kind: InitKind) -> FunctionBody {
        FunctionBody::SingleReturn(FunctionReturn {
            kind: Some(kind),
            init_object: None,
            init_array: None,
            cast: None,
        })
    }

    /// A declaration with fully annotated primitive params for call-site
    /// tests: `params` are `(name, type-text)` pairs, all exact-arity.
    fn callable(name: &str, params: Vec<(&str, &str)>) -> FunctionDecl {
        FunctionDecl {
            name: name.to_owned(),
            span: span(0, 10),
            scope: 0,
            symbol: None,
            params: params
                .into_iter()
                .map(|(param, ty)| FunctionParam {
                    name: param.to_owned(),
                    annotated: true,
                    annotation: Some(ty.to_owned()),
                    optional: false,
                    is_rest: false,
                })
                .collect(),
            params_complex: false,
            is_async: false,
            has_type_params: false,
            return_annotation: Some("number".to_owned()),
            body: single(InitKind::Number),
        }
    }

    /// One call site at `callee_span` with literal-kind args.
    fn call(callee: &str, callee_span: Span, args: Vec<(InitKind, Span)>) -> CallSite {
        CallSite {
            callee: callee.to_owned(),
            callee_span,
            span: span(0, 60),
            args: args
                .into_iter()
                .map(|(kind, arg_span)| CallArg {
                    kind,
                    span: arg_span,
                    cast: None,
                })
                .collect(),
        }
    }

    fn object_return(members: Vec<(&str, ObjectMemberKind)>) -> FunctionBody {
        FunctionBody::SingleReturn(FunctionReturn {
            kind: None,
            init_object: Some(ObjectInit {
                members: members
                    .into_iter()
                    .map(|(name, kind)| ObjectMemberInit {
                        name: name.to_owned(),
                        kind,
                    })
                    .collect(),
                fresh: true,
            }),
            init_array: None,
            cast: None,
        })
    }

    /// One literal return position for join tests.
    fn lit(kind: InitKind) -> FunctionReturn {
        FunctionReturn {
            kind: Some(kind),
            init_object: None,
            init_array: None,
            cast: None,
        }
    }

    /// One object-literal return position for join tests (always fresh: only
    /// direct syntactic literals carry member facts).
    fn obj(members: Vec<(&str, ObjectMemberKind)>) -> FunctionReturn {
        FunctionReturn {
            kind: None,
            init_object: Some(ObjectInit {
                members: members
                    .into_iter()
                    .map(|(name, kind)| ObjectMemberInit {
                        name: name.to_owned(),
                        kind,
                    })
                    .collect(),
                fresh: true,
            }),
            init_array: None,
            cast: None,
        }
    }

    /// Two sequential returns for join tests.
    fn sequence(first: FunctionReturn, second: FunctionReturn) -> FunctionBody {
        FunctionBody::SequenceReturns(JoinedReturns { first, second })
    }

    /// A guard-then-tail join for join tests.
    fn guard_join(guard: FunctionReturn, tail: FunctionReturn) -> FunctionBody {
        FunctionBody::GuardReturn(JoinedReturns {
            first: guard,
            second: tail,
        })
    }

    /// An if/else branch join for join tests.
    fn branches(then_branch: FunctionReturn, else_branch: FunctionReturn) -> FunctionBody {
        FunctionBody::BranchReturns(JoinedReturns {
            first: then_branch,
            second: else_branch,
        })
    }

    /// A try/catch body for try/catch tests: one return per arm plus an
    /// optional trailing return.
    fn try_catch(
        try_branch: FunctionReturn,
        catch_branch: FunctionReturn,
        tail: Option<FunctionReturn>,
    ) -> FunctionBody {
        FunctionBody::TryCatch(TryCatchBody {
            try_branch,
            catch_branch,
            tail,
        })
    }

    /// A switch body for switch tests: one return per case plus an
    /// optional default return.
    fn switched(cases: Vec<FunctionReturn>, default: Option<FunctionReturn>) -> FunctionBody {
        FunctionBody::Switch(SwitchBody { cases, default })
    }

    #[test]
    fn function_correct_is_silent_and_memoized() {
        let binder = binder_with(&[("add", span(0, 10)), ("point", span(11, 21))]);
        let decls = [
            function(
                "add",
                0,
                10,
                vec![("a", true), ("b", true)],
                Some("number"),
                single(InitKind::Number),
            ),
            function(
                "point",
                11,
                21,
                Vec::new(),
                Some("{ x: number; label: string }"),
                object_return(vec![
                    ("x", ObjectMemberKind::Number),
                    ("label", ObjectMemberKind::String),
                ]),
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(db.recompute_count(), 2);
        let repeat = check_functions(FILE, &decls, &binder, &mut db);
        assert!(repeat.diagnostics.is_empty());
        assert!(repeat.unsupported.is_empty());
        assert_eq!(db.recompute_count(), 2);
    }

    #[test]
    fn function_return_mismatch_is_pith2322() {
        let binder = binder_with(&[("pick", span(0, 10))]);
        let decls = [function(
            "pick",
            0,
            10,
            vec![("flag", true)],
            Some("number"),
            single(InitKind::String),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(0, 10));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn function_gates_are_unsupported_never_silent() {
        let binder = binder_with(&[
            ("pattern", span(0, 8)),
            ("param", span(9, 17)),
            ("ret", span(18, 26)),
            ("over", span(27, 35)),
        ]);
        let mut complex_params = function(
            "pattern",
            0,
            8,
            Vec::new(),
            Some("number"),
            single(InitKind::Number),
        );
        complex_params.params_complex = true;
        let unannotated_param = function(
            "param",
            9,
            17,
            vec![("value", false)],
            Some("number"),
            single(InitKind::Number),
        );
        let missing_return = function(
            "ret",
            18,
            26,
            vec![("n", true)],
            None,
            single(InitKind::Number),
        );
        let overload = function(
            "over",
            27,
            35,
            vec![("a", true)],
            Some("number"),
            FunctionBody::NoBody { declared: false },
        );
        let decls = [complex_params, unannotated_param, missing_return, overload];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 4);
        let los: Vec<u32> = report.unsupported.iter().map(|u| u.span.lo).collect();
        assert_eq!(los, [0, 9, 18, 27]);
        let reasons: Vec<&str> = report
            .unsupported
            .iter()
            .map(|u| u.reason.as_str())
            .collect();
        assert!(
            reasons[0].contains("parameter pattern"),
            "reason: {}",
            reasons[0]
        );
        assert!(reasons[1].contains("'value'"), "reason: {}", reasons[1]);
        assert!(
            reasons[2].contains("no return annotation"),
            "reason: {}",
            reasons[2]
        );
        assert!(reasons[3].contains("overload"), "reason: {}", reasons[3]);
    }

    #[test]
    fn function_body_gates_are_unsupported_never_silent() {
        let binder = binder_with(&[
            ("ambient", span(36, 44)),
            ("empty", span(45, 53)),
            ("branch", span(54, 62)),
            ("alias", span(63, 71)),
        ]);
        let ambient = function(
            "ambient",
            36,
            44,
            vec![("a", true)],
            Some("number"),
            FunctionBody::NoBody { declared: true },
        );
        let empty = function(
            "empty",
            45,
            53,
            Vec::new(),
            Some("void"),
            FunctionBody::Empty,
        );
        let branch = function(
            "branch",
            54,
            62,
            vec![("flag", true)],
            Some("number"),
            FunctionBody::Complex,
        );
        let alias = function(
            "alias",
            63,
            71,
            vec![("n", true)],
            Some("number"),
            single(InitKind::NonLiteral),
        );
        let decls = [ambient, empty, branch, alias];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 4);
        let los: Vec<u32> = report.unsupported.iter().map(|u| u.span.lo).collect();
        assert_eq!(los, [36, 45, 54, 63]);
        let reasons: Vec<&str> = report
            .unsupported
            .iter()
            .map(|u| u.reason.as_str())
            .collect();
        assert!(
            reasons[0].contains("declare function"),
            "reason: {}",
            reasons[0]
        );
        assert!(reasons[1].contains("empty"), "reason: {}", reasons[1]);
        assert!(reasons[2].contains("complex"), "reason: {}", reasons[2]);
        assert!(reasons[3].contains("non-literal"), "reason: {}", reasons[3]);
    }

    #[test]
    fn function_unknown_return_annotation_is_pith2304() {
        // Delegation proof: unknown return names diagnose like annotations.
        let binder = binder_with(&[("f", span(0, 10))]);
        let decls = [function(
            "f",
            0,
            10,
            Vec::new(),
            Some("Nope"),
            single(InitKind::Number),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
    }

    #[test]
    fn function_object_return_wrong_member_is_pith2322() {
        // Delegation proof: object returns run the shared object machinery.
        let binder = binder_with(&[("point", span(0, 10))]);
        let decls = [function(
            "point",
            0,
            10,
            Vec::new(),
            Some("{ x: number; label: string }"),
            object_return(vec![
                ("x", ObjectMemberKind::String),
                ("label", ObjectMemberKind::String),
            ]),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn sequence_returns_check_each_position() {
        // P023 join rule (probed tsc 7.0.2): two wrong sequential returns
        // report twice, once per position. Per-position occurrence nodes
        // memoize separately (two recomputes, never one aliased entry).
        let binder = binder_with(&[("pair", span(0, 10))]);
        let decls = [function(
            "pair",
            0,
            10,
            Vec::new(),
            Some("number"),
            sequence(lit(InitKind::String), lit(InitKind::String)),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 2);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert_eq!(
                diag.message,
                "Type 'string' is not assignable to type 'number'."
            );
        }
        assert_eq!(db.recompute_count(), 2);
    }

    #[test]
    fn unreachable_return_still_checks() {
        // Probed tsc 7.0.2: the unreachable position still verdicts, so a
        // clean-then-wrong sequence reports its second return and a
        // wrong-then-clean one its first.
        let binder = binder_with(&[("second_wrong", span(0, 10)), ("first_wrong", span(11, 21))]);
        let decls = [
            function(
                "second_wrong",
                0,
                10,
                Vec::new(),
                Some("number"),
                sequence(lit(InitKind::Number), lit(InitKind::String)),
            ),
            function(
                "first_wrong",
                11,
                21,
                Vec::new(),
                Some("number"),
                sequence(lit(InitKind::String), lit(InitKind::Number)),
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 2);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert_eq!(
                diag.message,
                "Type 'string' is not assignable to type 'number'."
            );
        }
    }

    #[test]
    fn branch_returns_diagnose_per_branch() {
        // Probed tsc 7.0.2: `if/else` with a return in each branch reports
        // per branch (one side wrong reports once; both wrong report twice).
        let binder = binder_with(&[("pick", span(0, 10)), ("both", span(11, 21))]);
        let decls = [
            function(
                "pick",
                0,
                10,
                vec![("flag", true)],
                Some("number"),
                branches(lit(InitKind::Number), lit(InitKind::String)),
            ),
            function(
                "both",
                11,
                21,
                vec![("flag", true)],
                Some("number"),
                branches(lit(InitKind::String), lit(InitKind::String)),
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 3);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert_eq!(
                diag.message,
                "Type 'string' is not assignable to type 'number'."
            );
        }
    }

    #[test]
    fn guard_tail_checks_both_positions() {
        // Probed tsc 7.0.2: a wrong guard return and a wrong tail return
        // each report at their own position.
        let binder = binder_with(&[("guarded", span(0, 10)), ("tailed", span(11, 21))]);
        let decls = [
            function(
                "guarded",
                0,
                10,
                vec![("x", true)],
                Some("string"),
                guard_join(lit(InitKind::Number), lit(InitKind::String)),
            ),
            function(
                "tailed",
                11,
                21,
                vec![("x", true)],
                Some("string"),
                guard_join(lit(InitKind::String), lit(InitKind::Number)),
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 2);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert_eq!(
                diag.message,
                "Type 'number' is not assignable to type 'string'."
            );
        }
    }

    #[test]
    fn join_non_literal_position_declines_whole_body() {
        // No partial verdicts: one unrepresentable position declines the
        // whole declaration with a position-naming reason.
        let binder = binder_with(&[("guarded", span(0, 10)), ("pick", span(11, 21))]);
        let decls = [
            function(
                "guarded",
                0,
                10,
                vec![("x", true)],
                Some("string"),
                guard_join(lit(InitKind::String), lit(InitKind::NonLiteral)),
            ),
            function(
                "pick",
                11,
                21,
                vec![("flag", true)],
                Some("string"),
                branches(lit(InitKind::NonLiteral), lit(InitKind::String)),
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 2);
        let reasons: Vec<&str> = report
            .unsupported
            .iter()
            .map(|u| u.reason.as_str())
            .collect();
        assert!(reasons[0].contains("tail return"), "reason: {}", reasons[0]);
        assert!(
            reasons[1].contains("then-branch return"),
            "reason: {}",
            reasons[1]
        );
    }

    #[test]
    fn try_catch_diagnoses_per_arm() {
        // Probed tsc 7.0.2 (P039): each `try`/`catch` arm checks
        // independently — one side wrong reports once, both wrong twice.
        let binder = binder_with(&[("pick", span(0, 10)), ("both", span(11, 21))]);
        let decls = [
            function(
                "pick",
                0,
                10,
                Vec::new(),
                Some("number"),
                try_catch(lit(InitKind::Number), lit(InitKind::String), None),
            ),
            function(
                "both",
                11,
                21,
                Vec::new(),
                Some("number"),
                try_catch(lit(InitKind::String), lit(InitKind::String), None),
            ),
        ];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 3);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert_eq!(
                diag.message,
                "Type 'string' is not assignable to type 'number'."
            );
        }
    }

    #[test]
    fn try_catch_tail_checks_as_third_position() {
        // Probed tsc 7.0.2 (P039): a trailing `return` after the `try`
        // statement checks as another position — clean arms plus a wrong
        // tail report once, at the tail.
        let binder = binder_with(&[("tailed", span(0, 10))]);
        let decls = [function(
            "tailed",
            0,
            10,
            Vec::new(),
            Some("number"),
            try_catch(
                lit(InitKind::Number),
                lit(InitKind::Number),
                Some(lit(InitKind::String)),
            ),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn try_catch_non_literal_arm_declines_whole_body() {
        // No partial verdicts: one identifier (non-literal) arm declines
        // the whole declaration with a position-naming reason, even when
        // the other arm is clean.
        let binder = binder_with(&[("thrown", span(0, 10))]);
        let decls = [function(
            "thrown",
            0,
            10,
            Vec::new(),
            Some("number"),
            try_catch(lit(InitKind::NonLiteral), lit(InitKind::Number), None),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("non-literal try return"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn try_unsupported_declines_with_recorded_reason() {
        // Frontend-recorded try/catch declines (`finally`, destructured
        // catch pattern, `throw`, non-straight arm) surface verbatim — never a verdict.
        let binder = binder_with(&[("finalized", span(0, 10))]);
        let decls = [function(
            "finalized",
            0,
            10,
            Vec::new(),
            Some("number"),
            FunctionBody::TryUnsupported {
                reason: "finally clause is outside the subset".to_owned(),
            },
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(
            report.unsupported[0].reason,
            "finally clause is outside the subset"
        );
    }

    #[test]
    fn switch_diagnoses_per_case() {
        // P040 switch rule (probed tsc 7.0.2): a wrong case and a wrong
        // default each report once, at their own position through the
        // synthetic delegation — two wrong cases report twice.
        let binder = binder_with(&[("pick", span(0, 10))]);
        let decls = [function(
            "pick",
            0,
            10,
            Vec::new(),
            Some("number"),
            switched(
                vec![lit(InitKind::String), lit(InitKind::String)],
                Some(lit(InitKind::Number)),
            ),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 2);
        for diag in &report.diagnostics {
            assert_eq!(diag.code, CODE_MISMATCH);
            assert_eq!(
                diag.message,
                "Type 'string' is not assignable to type 'number'."
            );
        }
        assert_eq!(db.recompute_count(), 3);
    }

    #[test]
    fn switch_non_literal_case_declines_whole_body() {
        // No partial verdicts: one identifier (non-literal) case declines
        // the whole declaration with a position-naming reason, even when
        // the other positions are clean.
        let binder = binder_with(&[("branched", span(0, 10))]);
        let decls = [function(
            "branched",
            0,
            10,
            Vec::new(),
            Some("number"),
            switched(
                vec![lit(InitKind::NonLiteral), lit(InitKind::Number)],
                Some(lit(InitKind::Number)),
            ),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("non-literal case return"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn switch_unsupported_declines_with_recorded_reason() {
        // Frontend-recorded switch declines (fallthrough, complex case,
        // declarations, non-literal discriminant or label, duplicate
        // default) surface verbatim — never a verdict.
        let binder = binder_with(&[("fallen", span(0, 10))]);
        let decls = [function(
            "fallen",
            0,
            10,
            Vec::new(),
            Some("number"),
            FunctionBody::SwitchUnsupported {
                reason: "fallthrough case is outside the subset".to_owned(),
            },
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(
            report.unsupported[0].reason,
            "fallthrough case is outside the subset"
        );
    }

    #[test]
    fn join_object_excess_is_per_occurrence() {
        // Freshness is per return position (H-002): the clean first object
        // stays silent while the second diagnoses its excess member.
        let binder = binder_with(&[("point", span(0, 10))]);
        let decls = [function(
            "point",
            0,
            10,
            Vec::new(),
            Some("{ x: number }"),
            sequence(
                obj(vec![("x", ObjectMemberKind::Number)]),
                obj(vec![
                    ("x", ObjectMemberKind::Number),
                    ("extra", ObjectMemberKind::String),
                ]),
            ),
        )];
        let mut db = QueryDb::new();
        let report = check_functions(FILE, &decls, &binder, &mut db);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_EXCESS_MEMBER);
        assert_eq!(
            report.diagnostics[0].message,
            "Object literal may only specify known properties, and 'extra' does not exist in type '{ x: number; }'."
        );
    }

    #[test]
    fn function_node_space_is_disjoint_from_consts() {
        // Consts and functions for one file share a db in the real pipeline:
        // same-position occurrence nodes must not alias memo entries (a
        // same-index const `number` and function `string` would trip the
        // memo debug_assert if they shared a node).
        let binder = binder_with(&[("a", span(0, 10)), ("f", span(11, 21))]);
        let consts = [decl("a", 0, 10, "number", InitKind::Number)];
        let funcs = [function(
            "f",
            11,
            21,
            Vec::new(),
            Some("string"),
            single(InitKind::String),
        )];
        let mut db = QueryDb::new();
        let const_report = check_file(FILE, &consts, &binder, &mut db);
        assert!(const_report.diagnostics.is_empty());
        let func_report = check_functions(FILE, &funcs, &binder, &mut db);
        assert!(func_report.diagnostics.is_empty());
        assert!(func_report.unsupported.is_empty());
        assert_eq!(db.recompute_count(), 2);
    }

    #[test]
    fn call_correct_is_silent() {
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        let calls = [call(
            "add",
            span(20, 23),
            vec![
                (InitKind::Number, span(24, 25)),
                (InitKind::Number, span(27, 28)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
    }

    #[test]
    fn call_too_few_is_pith2554_at_callee() {
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        let calls = [call(
            "add",
            span(20, 23),
            vec![(InitKind::Number, span(24, 25))],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(report.diagnostics[0].span, span(20, 23));
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 arguments, but got 1."
        );
    }

    #[test]
    fn call_too_many_is_pith2554_at_excess_arg() {
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        let calls = [call(
            "add",
            span(20, 23),
            vec![
                (InitKind::Number, span(24, 25)),
                (InitKind::Number, span(27, 28)),
                (InitKind::Number, span(30, 31)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(report.diagnostics[0].span, span(30, 31));
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 arguments, but got 3."
        );
    }

    #[test]
    fn call_wrong_arg_type_is_pith2345_at_arg() {
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        let calls = [call(
            "add",
            span(20, 23),
            vec![
                (InitKind::Number, span(24, 25)),
                (InitKind::String, span(27, 33)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(report.diagnostics[0].span, span(27, 33));
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
    }

    #[test]
    fn call_arity_beats_arg_type() {
        // Probed on tsc 7.0.2: `add("oops")` against two `number` params
        // reports only TS2554 — one family per call site, arity first.
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        let calls = [call(
            "add",
            span(20, 23),
            vec![(InitKind::String, span(24, 30))],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 arguments, but got 1."
        );
    }

    #[test]
    fn call_reports_first_mismatch_only() {
        // Probed on tsc 7.0.2: `add("x", "y")` reports one TS2345 at the
        // first argument, never one per argument.
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        let calls = [call(
            "add",
            span(20, 23),
            vec![
                (InitKind::String, span(24, 27)),
                (InitKind::String, span(29, 32)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(report.diagnostics[0].span, span(24, 27));
    }

    #[test]
    fn call_non_literal_arg_skips_type_but_not_arity() {
        let binder = calls_binder(&[("add", span(0, 10))], &[]);
        let decls = [callable("add", vec![("a", "number"), ("b", "number")])];
        // An identifier argument degrades per-argument: the literal second
        // argument still checks.
        let typed = [call(
            "add",
            span(20, 23),
            vec![
                (InitKind::NonLiteral, span(24, 25)),
                (InitKind::String, span(27, 33)),
            ],
        )];
        let typed_report = check_calls(FILE, &decls, &typed, &binder);
        assert_eq!(typed_report.diagnostics.len(), 1);
        assert_eq!(typed_report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(typed_report.diagnostics[0].span, span(27, 33));
        // Arity still enforces over non-literal arguments.
        let short = [call(
            "add",
            span(40, 43),
            vec![(InitKind::NonLiteral, span(44, 45))],
        )];
        let short_report = check_calls(FILE, &decls, &short, &binder);
        assert_eq!(short_report.diagnostics.len(), 1);
        assert_eq!(short_report.diagnostics[0].code, CODE_ARITY);
    }

    #[test]
    fn call_unresolved_callee_skips_silently() {
        // The oracle reports TS2304 here; the solver stays silent because
        // the name is already tracked as an unresolved reference — never a
        // double diagnosis.
        let binder = calls_binder(&[], &["missing"]);
        let decls: Vec<FunctionDecl> = Vec::new();
        let calls = [call(
            "missing",
            span(0, 7),
            vec![(InitKind::Number, span(8, 9))],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
    }

    #[test]
    fn call_untracked_name_is_unsupported_not_silent() {
        // Neither declared nor unresolved-tracked: driver skew, recorded
        // rather than silently dropped.
        let binder = calls_binder(&[], &[]);
        let decls: Vec<FunctionDecl> = Vec::new();
        let calls = [call("ghost", span(0, 5), Vec::new())];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("nothing to check against"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn call_multiple_declarations_decline() {
        // Two bodied declarations of one name mean shadowing, not overloads:
        // implementations cannot be disambiguated, so one unsupported note
        // (bodiless overload signatures resolve instead — see the P044
        // tests below).
        let binder = calls_binder(&[("over", span(0, 10))], &[]);
        let decls = [
            callable("over", vec![("a", "number")]),
            callable("over", vec![("a", "string")]),
        ];
        let calls = [call(
            "over",
            span(30, 34),
            vec![
                (InitKind::Number, span(35, 36)),
                (InitKind::Number, span(38, 39)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.unsupported[0].span, span(30, 34));
        assert!(
            report.unsupported[0]
                .reason
                .contains("multiple declarations"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    /// An overload signature declaration: fully annotated primitive params
    /// with no body (fact-fed from one `NoBody` overload signature).
    fn overload_sig(name: &str, params: Vec<FunctionParam>) -> FunctionDecl {
        FunctionDecl {
            name: name.to_owned(),
            span: span(0, 10),
            scope: 0,
            symbol: None,
            params,
            params_complex: false,
            is_async: false,
            has_type_params: false,
            return_annotation: Some("number".to_owned()),
            body: FunctionBody::NoBody { declared: false },
        }
    }

    /// One exact-arity annotated primitive parameter for overload tests.
    fn fixed_param(name: &str, ty: &str) -> FunctionParam {
        FunctionParam {
            name: name.to_owned(),
            annotated: true,
            annotation: Some(ty.to_owned()),
            optional: false,
            is_rest: false,
        }
    }

    /// One optional annotated primitive parameter for overload tests.
    fn optional_param(name: &str, ty: &str) -> FunctionParam {
        FunctionParam {
            name: name.to_owned(),
            annotated: true,
            annotation: Some(ty.to_owned()),
            optional: true,
            is_rest: false,
        }
    }

    #[test]
    fn overload_any_match_is_silent() {
        // Probed tsc 7.0.2 P044: a call is clean when ANY signature admits
        // it — a first-signature mismatch never surfaces when a later one
        // matches, and vice versa. The `(a: any)` implementation never
        // participates (it would admit every call below, yet verdicts still
        // follow the signatures).
        let binder = calls_binder(&[("pick", span(0, 10))], &[]);
        let decls = [
            overload_sig("pick", vec![fixed_param("a", "number")]),
            overload_sig("pick", vec![fixed_param("a", "string")]),
            callable("pick", vec![("a", "any")]),
        ];
        let first_match = [call(
            "pick",
            span(20, 24),
            vec![(InitKind::Number, span(25, 26))],
        )];
        let report = check_calls(FILE, &decls, &first_match, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        let second_match = [call(
            "pick",
            span(30, 34),
            vec![(InitKind::String, span(35, 39))],
        )];
        let report = check_calls(FILE, &decls, &second_match, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
    }

    #[test]
    fn overload_all_fail_is_pith2769_at_last_signature() {
        // Probed tsc 7.0.2 P044: every arity-compatible signature fails on
        // types, so the call spells `TS2769` elaborating the LAST
        // signature's first mismatch at that argument.
        let binder = calls_binder(&[("pick", span(0, 10))], &[]);
        let decls = [
            overload_sig("pick", vec![fixed_param("a", "number")]),
            overload_sig("pick", vec![fixed_param("a", "string")]),
            callable("pick", vec![("a", "any")]),
        ];
        let calls = [call(
            "pick",
            span(20, 24),
            vec![(InitKind::Boolean, span(25, 29))],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_OVERLOAD);
        assert_eq!(report.diagnostics[0].span, span(25, 29));
        assert_eq!(
            report.diagnostics[0].message,
            "No overload matches this call.\n  The last overload gave the following error.\n    \
            Argument of type 'boolean' is not assignable to parameter of type 'string'."
        );
    }

    #[test]
    fn overload_single_compatible_checks_like_lone_declaration() {
        // Probed tsc 7.0.2 P044: exactly one arity-compatible signature
        // reports its own `TS2345` at the first mismatch.
        let binder = calls_binder(&[("opt", span(0, 10))], &[]);
        let decls = [
            overload_sig(
                "opt",
                vec![fixed_param("a", "number"), optional_param("b", "number")],
            ),
            overload_sig("opt", vec![fixed_param("a", "string")]),
            callable("opt", vec![("a", "any"), ("b", "any")]),
        ];
        let calls = [call(
            "opt",
            span(20, 23),
            vec![
                (InitKind::String, span(24, 27)),
                (InitKind::Number, span(29, 30)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(report.diagnostics[0].span, span(24, 27));
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
    }

    #[test]
    fn overload_union_arity_is_pith2554() {
        // Probed tsc 7.0.2 P044: no signature admits the count, so the call
        // unions to `TS2554` (exact here) at the first excess argument.
        let binder = calls_binder(&[("over", span(0, 10))], &[]);
        let decls = [
            overload_sig("over", vec![fixed_param("a", "number")]),
            overload_sig("over", vec![fixed_param("a", "string")]),
            callable("over", vec![("a", "any")]),
        ];
        let calls = [call(
            "over",
            span(30, 34),
            vec![
                (InitKind::Number, span(35, 36)),
                (InitKind::Number, span(38, 39)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(report.diagnostics[0].span, span(38, 39));
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 1 arguments, but got 2."
        );
    }

    #[test]
    fn overload_gap_is_pith2575() {
        // Probed tsc 7.0.2 P044: the count falls strictly between admitted
        // ranges, so the call spells the gap diagnostic at the callee,
        // naming the nearest signature minimums below and above.
        let binder = calls_binder(&[("d", span(0, 10))], &[]);
        let decls = [
            overload_sig("d", vec![fixed_param("a", "number")]),
            overload_sig(
                "d",
                vec![
                    fixed_param("a", "number"),
                    fixed_param("b", "number"),
                    fixed_param("c", "number"),
                ],
            ),
            callable("d", vec![("a", "any")]),
        ];
        let calls = [call(
            "d",
            span(30, 31),
            vec![
                (InitKind::Number, span(32, 33)),
                (InitKind::Number, span(35, 36)),
            ],
        )];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_OVERLOAD_ARITY);
        assert_eq!(report.diagnostics[0].span, span(30, 31));
        assert_eq!(
            report.diagnostics[0].message,
            "No overload expects 2 arguments, but overloads do exist that expect either 1 or 3 \
            arguments."
        );
    }

    #[test]
    fn overload_generic_signature_declines_distinctly() {
        // The oracle admits generic signatures (a pinned oracle-clean
        // divergence), so the solver excludes them with a distinct reason:
        // a call a remaining signature admits stays clean, while a call
        // none admits declines with the exclusion recorded — never a forced
        // `TS2769`.
        let binder = calls_binder(&[("g", span(0, 10))], &[]);
        let mut generic = overload_sig("g", vec![fixed_param("a", "T")]);
        generic.has_type_params = true;
        let decls = [
            generic,
            overload_sig("g", vec![fixed_param("a", "number")]),
            callable("g", vec![("a", "any")]),
        ];
        let clean = [call(
            "g",
            span(20, 21),
            vec![(InitKind::Number, span(22, 23))],
        )];
        let report = check_calls(FILE, &decls, &clean, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        let declined = [call(
            "g",
            span(30, 31),
            vec![(InitKind::Boolean, span(32, 38))],
        )];
        let report = check_calls(FILE, &decls, &declined, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("generic type parameters"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn call_param_gates_are_unsupported_never_silent() {
        let binder = calls_binder(&[], &[]);
        let mut unannotated = callable("u", vec![("v", "number")]);
        unannotated.params[0].annotated = false;
        unannotated.params[0].annotation = None;
        let mut after = callable("o", vec![("a", "number"), ("b", "number")]);
        after.params[0].optional = true;
        let mut non_array_rest = callable("r", vec![("items", "number")]);
        non_array_rest.params[0].is_rest = true;
        let union = callable("n", vec![("v", "number | string")]);
        let unknown = callable("w", vec![("v", "Nope")]);
        let mut complex = callable("c", vec![("v", "number")]);
        complex.params_complex = true;
        let decls = [unannotated, after, non_array_rest, union, unknown, complex];
        let calls = [
            call("u", span(0, 1), vec![(InitKind::Number, span(2, 3))]),
            call("o", span(10, 11), vec![(InitKind::Number, span(12, 13))]),
            call("r", span(20, 21), vec![(InitKind::Number, span(22, 23))]),
            call("n", span(30, 31), vec![(InitKind::Number, span(32, 33))]),
            call("w", span(40, 41), vec![(InitKind::Number, span(42, 43))]),
            call("c", span(50, 51), vec![(InitKind::Number, span(52, 53))]),
        ];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 6);
        let los: Vec<u32> = report.unsupported.iter().map(|note| note.span.lo).collect();
        assert_eq!(los, [0, 10, 20, 30, 40, 50]);
        let reasons: Vec<&str> = report
            .unsupported
            .iter()
            .map(|note| note.reason.as_str())
            .collect();
        assert!(
            reasons[0].contains("unannotated parameter"),
            "reason: {}",
            reasons[0]
        );
        assert!(
            reasons[1].contains("follows an optional parameter"),
            "reason: {}",
            reasons[1]
        );
        assert!(
            reasons[2].contains("must be of an array type"),
            "reason: {}",
            reasons[2]
        );
        assert!(
            reasons[3].contains("union parameter type"),
            "reason: {}",
            reasons[3]
        );
        assert!(
            reasons[4].contains("parameter type"),
            "reason: {}",
            reasons[4]
        );
        assert!(
            reasons[5].contains("non-identifier parameter pattern"),
            "reason: {}",
            reasons[5]
        );
    }

    #[test]
    fn range_and_rest_arities_check() {
        // `f(a: number, b?: number)`: 1-2 admit, 0 and 3 diagnose with the
        // range spelling; `h(a: number, ...rest: number[])`: 0 diagnoses
        // `TS2555`, extras check against the element type.
        let binder = calls_binder(&[], &[]);
        let mut optional = callable("f", vec![("a", "number"), ("b", "number")]);
        optional.params[1].optional = true;
        let mut rest = callable("h", vec![("a", "number"), ("items", "number[]")]);
        rest.params[1].is_rest = true;
        let decls = [optional, rest];
        let nullary = Vec::new();
        let calls = [
            call("f", span(0, 1), nullary.clone()),
            call(
                "f",
                span(10, 11),
                vec![
                    (InitKind::Number, span(12, 13)),
                    (InitKind::Number, span(14, 15)),
                    (InitKind::Number, span(16, 17)),
                ],
            ),
            call("h", span(20, 21), nullary.clone()),
            call(
                "h",
                span(30, 31),
                vec![
                    (InitKind::Number, span(32, 33)),
                    (InitKind::String, span(34, 35)),
                ],
            ),
        ];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 4);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(report.diagnostics[0].span, span(0, 1));
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 1-2 arguments, but got 0."
        );
        assert_eq!(report.diagnostics[1].code, CODE_ARITY);
        assert_eq!(report.diagnostics[1].span, span(16, 17));
        assert_eq!(
            report.diagnostics[1].message,
            "Expected 1-2 arguments, but got 3."
        );
        assert_eq!(report.diagnostics[2].code, CODE_ARITY_MIN);
        assert_eq!(report.diagnostics[2].span, span(20, 21));
        assert_eq!(
            report.diagnostics[2].message,
            "Expected at least 1 arguments, but got 0."
        );
        assert_eq!(report.diagnostics[3].code, CODE_ARG_TYPE);
        assert_eq!(report.diagnostics[3].span, span(34, 35));
        assert_eq!(
            report.diagnostics[3].message,
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
    }

    #[test]
    fn explicit_undefined_is_silent_only_at_optional_positions() {
        // Probed tsc 7.0.2 P037: `f(1, undefined)` over `(a: number, b?:
        // number)` is silent, while the same `undefined` at the fixed
        // position and at a rest extra both diagnose `TS2345`.
        let binder = calls_binder(&[], &[]);
        let mut optional = callable("f", vec![("a", "number"), ("b", "number")]);
        optional.params[1].optional = true;
        let mut rest = callable("h", vec![("a", "number"), ("items", "number[]")]);
        rest.params[1].is_rest = true;
        let decls = [optional, rest];
        let calls = [
            call(
                "f",
                span(0, 1),
                vec![
                    (InitKind::Number, span(2, 3)),
                    (InitKind::Undefined, span(4, 5)),
                ],
            ),
            call("f", span(10, 11), vec![(InitKind::Undefined, span(12, 13))]),
            call(
                "h",
                span(20, 21),
                vec![
                    (InitKind::Number, span(22, 23)),
                    (InitKind::Undefined, span(24, 25)),
                ],
            ),
        ];
        let report = check_calls(FILE, &decls, &calls, &binder);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(report.diagnostics[0].span, span(12, 13));
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'undefined' is not assignable to parameter of type 'number'."
        );
        assert_eq!(report.diagnostics[1].code, CODE_ARG_TYPE);
        assert_eq!(report.diagnostics[1].span, span(24, 25));
    }

    fn union_decl(name: &str, lo: u32, hi: u32, ann: &str, init: Option<InitKind>) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some(ann.to_owned()),
            init,
            init_object: None,
            init_array: None,
            cast: None,
        }
    }

    fn unknown_decl(name: &str, lo: u32, hi: u32, init: Option<InitKind>) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            kind: DeclKind::Const,
            annotation: Some("unknown".to_owned()),
            init,
            init_object: None,
            init_array: None,
            cast: None,
        }
    }

    fn narrowing_use(
        name: &str,
        lo: u32,
        hi: u32,
        annotation: &str,
        target: &str,
        init_lo: u32,
        init_hi: u32,
    ) -> NarrowedUse {
        NarrowedUse {
            name: name.to_owned(),
            span: span(lo, hi),
            scope: 0,
            symbol: None,
            annotation: annotation.to_owned(),
            target: target.to_owned(),
            init_span: span(init_lo, init_hi),
        }
    }

    /// Guard region spans, bundled so the `guard` test helper stays lean.
    #[derive(Clone, Copy, Debug)]
    struct GuardSpans {
        then: Span,
        else_: Option<Span>,
        if_: Span,
    }

    fn guard_spans(
        then_lo: u32,
        then_hi: u32,
        else_span: Option<(u32, u32)>,
        if_lo: u32,
        if_hi: u32,
    ) -> GuardSpans {
        GuardSpans {
            then: span(then_lo, then_hi),
            else_: else_span.map(|(lo, hi)| span(lo, hi)),
            if_: span(if_lo, if_hi),
        }
    }

    fn guard(
        target: &str,
        matched: &str,
        negated: bool,
        early_return: bool,
        spans: GuardSpans,
    ) -> TypeofGuard {
        TypeofGuard {
            target: target.to_owned(),
            matched: matched.to_owned(),
            negated,
            then_span: spans.then,
            else_span: spans.else_,
            early_return,
            if_span: spans.if_,
        }
    }

    fn narrow_report(
        decls: &[ConstDecl],
        uses: &[NarrowedUse],
        guards: &[TypeofGuard],
        declines: &[DeclineRegion],
        binder: &Binder,
    ) -> FileReport {
        let mut db = QueryDb::new();
        let facts = NarrowingFacts {
            uses,
            guards,
            declines,
        };
        check_narrowing(FILE, decls, &facts, binder, &mut db)
    }

    #[test]
    fn union_decl_literal_verdicts_use_canonical_spelling() {
        // Source order never drives the spelling: `string | number` reads
        // back canonically in both positions (probed tsc 7.0.2).
        let binder = binder_with(&[("ok", span(0, 10)), ("bad", span(11, 21))]);
        let decls = [
            union_decl("ok", 0, 10, "number | string", Some(InitKind::Number)),
            union_decl(
                "bad",
                11,
                21,
                "boolean | number | string",
                Some(InitKind::Null),
            ),
        ];
        let report = narrow_report(&decls, &[], &[], &[], &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(11, 21));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'null' is not assignable to type 'string | number | boolean'."
        );
    }

    #[test]
    fn union_decl_unknown_member_is_pith2304() {
        // Mirrors the object member rule: unknown names diagnose, shapes decline.
        let binder = binder_with(&[("u", span(0, 8)), ("s", span(9, 17))]);
        let decls = [
            union_decl("u", 0, 8, "number | Nope", Some(InitKind::Number)),
            union_decl("s", 9, 17, "number | string[]", Some(InitKind::Number)),
        ];
        let report = narrow_report(&decls, &[], &[], &[], &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("outside the subset"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn narrowing_guarded_match_is_silent() {
        let binder = binder_with(&[("x", span(0, 10)), ("greeting", span(40, 60))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("greeting", 40, 60, "string", "x", 58, 59)];
        let guards = [guard(
            "x",
            "string",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        // The `declare const` target itself has nothing to check.
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn narrowing_guarded_mismatch_is_pith2322() {
        let binder = binder_with(&[("x", span(0, 10)), ("count", span(40, 60))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("count", 40, 60, "number", "x", 58, 59)];
        let guards = [guard(
            "x",
            "string",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn narrowing_negated_branches_flip() {
        // `!==` then refines to the complement; `else` refines back.
        let binder = binder_with(&[
            ("x", span(0, 10)),
            ("count", span(40, 60)),
            ("other", span(80, 100)),
        ]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [
            narrowing_use("count", 40, 60, "number", "x", 58, 59),
            narrowing_use("other", 80, 100, "number", "x", 98, 99),
        ];
        let guards = [guard(
            "x",
            "string",
            true,
            false,
            guard_spans(20, 70, Some((70, 110)), 10, 110),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(80, 100));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn narrowing_early_return_refines_after() {
        let binder = binder_with(&[
            ("x", span(0, 10)),
            ("ok", span(80, 90)),
            ("bad", span(95, 105)),
        ]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [
            narrowing_use("ok", 80, 90, "string", "x", 88, 89),
            narrowing_use("bad", 95, 105, "number", "x", 103, 104),
        ];
        let guards = [guard(
            "x",
            "string",
            true,
            true,
            guard_spans(20, 40, None, 10, 40),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(95, 105));
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn narrowing_unguarded_use_diagnoses_full_union() {
        let binder = binder_with(&[("x", span(0, 10)), ("bad", span(20, 30))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("bad", 20, 30, "boolean", "x", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string | number' is not assignable to type 'boolean'."
        );
    }

    #[test]
    fn narrowing_decline_regions_are_unsupported_never_silent() {
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(40, 50))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("a", 40, 50, "number", "x", 48, 49)];
        let declines = [DeclineRegion {
            span: span(20, 70),
            reason: "guard condition is not a simple typeof comparison: outside the subset"
                .to_owned(),
        }];
        let report = narrow_report(&decls, &uses, &[], &declines, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("outside the subset"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn narrowing_outsider_literal_declines_matched_side() {
        // `boolean` is not in `number | string`: the then region is `never`
        // (silent in tsc), so the solver declines instead of verdicting.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(40, 50))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("a", 40, 50, "number", "x", 48, 49)];
        let guards = [guard(
            "x",
            "boolean",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("never"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn narrowing_outsider_complement_checks_full_union() {
        // `else` of `=== "boolean"` over `number | string` is the full union.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(80, 90))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("a", 80, 90, "boolean", "x", 88, 89)];
        let guards = [guard(
            "x",
            "boolean",
            false,
            false,
            guard_spans(20, 70, Some((70, 100)), 10, 100),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string | number' is not assignable to type 'boolean'."
        );
    }

    #[test]
    fn narrowing_multi_member_complement_declines() {
        // Complement `number | boolean` is not a single primitive.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(80, 90))]);
        let decls = [union_decl("x", 0, 10, "string | number | boolean", None)];
        let uses = [narrowing_use("a", 80, 90, "number", "x", 88, 89)];
        let guards = [guard(
            "x",
            "string",
            false,
            false,
            guard_spans(20, 70, Some((70, 100)), 10, 100),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1]
                .reason
                .contains("not a single primitive"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn narrowing_overlapping_guards_must_agree() {
        // Two applicable guards refining differently decline; agreeing ones check.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(40, 50))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("a", 40, 50, "number", "x", 48, 49)];
        let disagree = [
            guard(
                "x",
                "string",
                false,
                false,
                guard_spans(20, 70, None, 10, 70),
            ),
            guard(
                "x",
                "number",
                false,
                false,
                guard_spans(20, 70, None, 10, 70),
            ),
        ];
        let report = narrow_report(&decls, &uses, &disagree, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("differently"),
            "reason: {}",
            report.unsupported[1].reason
        );
        let agree = [
            guard(
                "x",
                "string",
                false,
                false,
                guard_spans(20, 70, None, 10, 70),
            ),
            guard(
                "x",
                "string",
                false,
                true,
                guard_spans(20, 70, None, 10, 20),
            ),
        ];
        let report = narrow_report(&decls, &uses, &agree, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn narrowing_literal_init_target_declines() {
        // Literal-initialized consts do not narrow (probed tsc 7.0.2): the
        // declaration checks against the union, guarded uses decline.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(40, 50))]);
        let decls = [union_decl(
            "x",
            0,
            10,
            "number | string",
            Some(InitKind::Number),
        )];
        let uses = [narrowing_use("a", 40, 50, "string", "x", 48, 49)];
        let guards = [guard(
            "x",
            "string",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("literal initializer"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn narrowing_shadowed_target_declines() {
        // Real shadowing needs two scopes: the inner `x` binds its own
        // symbol, so its missing-init note anchors at (60, 70) and the use's
        // shadowed-target note sorts between the two declarations.
        let mut binder = Binder::new();
        binder.build_file(
            FILE,
            &[
                ScopeInput {
                    index: 0,
                    parent: u32::MAX,
                },
                ScopeInput {
                    index: 1,
                    parent: 0,
                },
            ],
            &[
                SymbolInput {
                    scope: 0,
                    name: "x".to_owned(),
                    span: span(0, 10),
                    flags: 0,
                },
                SymbolInput {
                    scope: 0,
                    name: "a".to_owned(),
                    span: span(40, 50),
                    flags: 0,
                },
                SymbolInput {
                    scope: 1,
                    name: "x".to_owned(),
                    span: span(60, 70),
                    flags: 0,
                },
            ],
            &[],
        );
        let inner = binder.resolve(FILE, 1, "x").expect("inner x resolves");
        let decls = [
            union_decl("x", 0, 10, "number | string", None),
            ConstDecl {
                name: "x".to_owned(),
                span: span(60, 70),
                scope: 1,
                symbol: Some(inner),
                kind: DeclKind::Const,
                annotation: Some("number | string".to_owned()),
                init: None,
                init_object: None,
                init_array: None,
                cast: None,
            },
        ];
        let uses = [narrowing_use("a", 40, 50, "string", "x", 48, 49)];
        let guards = [guard(
            "x",
            "string",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 3);
        assert!(
            report.unsupported[1].reason.contains("shadowed"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn narrowing_unknown_target_keeps_legacy_note() {
        // No union bears the name: exactly today's non-literal note, so a
        // future adapter migration changes no verdict.
        let binder = binder_with(&[("a", span(40, 50))]);
        let uses = [narrowing_use("a", 40, 50, "string", "ghost", 48, 49)];
        let report = narrow_report(&[], &uses, &[], &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(
            report.unsupported[0].reason,
            "non-literal initializer is outside the subset"
        );
    }

    #[test]
    fn narrowing_unknown_unguarded_use_diagnoses_unknown() {
        // `declare const uv: unknown` plus an unguarded use: tsc's exact
        // `unknown` spelling (probed 7.0.2 P033), not a decline.
        let binder = binder_with(&[("uv", span(0, 10)), ("a", span(20, 30))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("a", 20, 30, "string", "uv", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'string'."
        );
    }

    #[test]
    fn narrowing_unknown_literal_init_still_narrows() {
        // Unlike unions, literal-init `unknown` enters the environment
        // (probed 7.0.2 P033: no assignment narrowing is observable): the
        // declaration itself is clean and the unguarded use diagnoses.
        let binder = binder_with(&[("u", span(0, 10)), ("a", span(20, 30))]);
        let decls = [unknown_decl("u", 0, 10, Some(InitKind::String))];
        let uses = [narrowing_use("a", 20, 30, "string", "u", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert!(
            report.unsupported.is_empty(),
            "unsupported: {:?}",
            report.unsupported
        );
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'string'."
        );
    }

    #[test]
    fn narrowing_unknown_non_literal_init_notes_and_enters() {
        // Non-literal `unknown` initializers decline with a note like union
        // targets — and still enter, so uses diagnose.
        let binder = binder_with(&[("u", span(0, 10)), ("a", span(20, 30))]);
        let decls = [unknown_decl("u", 0, 10, Some(InitKind::NonLiteral))];
        let uses = [narrowing_use("a", 20, 30, "number", "u", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("non-literal"),
            "reason: {}",
            report.unsupported[0].reason
        );
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'number'."
        );
    }

    #[test]
    fn narrowing_unknown_guarded_match_is_silent() {
        let binder = binder_with(&[("uv", span(0, 10)), ("greeting", span(40, 60))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("greeting", 40, 60, "string", "uv", 58, 59)];
        let guards = [guard(
            "uv",
            "string",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        // The `declare const` target itself has nothing to check.
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn narrowing_unknown_guarded_mismatch_is_pith2322() {
        let binder = binder_with(&[("uv", span(0, 10)), ("count", span(40, 60))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("count", 40, 60, "number", "uv", 58, 59)];
        let guards = [guard(
            "uv",
            "string",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    #[test]
    fn narrowing_unknown_else_complement_diagnoses_unknown() {
        // The complement of one primitive in `unknown` is still `unknown`
        // (probed 7.0.2 P033) — never a narrowed single.
        let binder = binder_with(&[("uv", span(0, 10)), ("a", span(80, 90))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("a", 80, 90, "string", "uv", 88, 89)];
        let guards = [guard(
            "uv",
            "string",
            false,
            false,
            guard_spans(20, 40, Some((60, 110)), 10, 60),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'string'."
        );
    }

    #[test]
    fn narrowing_unknown_expected_is_silent() {
        // `unknown` into `unknown` is silent in tsc (probed P033) — no
        // diagnostic and no use note, just the declaration note.
        let binder = binder_with(&[("uv", span(0, 10)), ("again", span(20, 30))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("again", 20, 30, "unknown", "uv", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn narrowing_any_expected_is_silent_for_union() {
        // `any`-expected uses accept every narrowed flow (probed P033) —
        // the PITH2304 the old gating emitted was a mis-verdict.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(20, 30))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("a", 20, 30, "any", "x", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn narrowing_never_expected_diagnoses_like_any_other_t() {
        // Probed tsc 7.0.2 P033, both target kinds: unguarded unions spell
        // the full union, guarded positions the narrowed single.
        let binder = binder_with(&[("x", span(0, 10)), ("n", span(20, 30))]);
        let decls = [union_decl("x", 0, 10, "number | string", None)];
        let uses = [narrowing_use("n", 20, 30, "never", "x", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string | number' is not assignable to type 'never'."
        );
        let binder = binder_with(&[("uv", span(0, 10)), ("m", span(20, 30))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("m", 20, 30, "never", "uv", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'never'."
        );
    }

    #[test]
    fn narrowing_union_absorbs_unknown_member() {
        // `number | unknown` is `unknown` in tsc (probed P033): the
        // declaration enters an unknown target instead of diagnosing
        // `PITH2304` for the `unknown` piece.
        let binder = binder_with(&[("x", span(0, 10)), ("a", span(20, 30))]);
        let decls = [union_decl("x", 0, 10, "number | unknown", None)];
        let uses = [narrowing_use("a", 20, 30, "string", "x", 28, 29)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert_eq!(report.unsupported.len(), 1);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'unknown' is not assignable to type 'string'."
        );
    }

    #[test]
    fn narrowing_unknown_object_guard_declines() {
        // `typeof uv === "object"` refines to `object | null` in tsc
        // (probed P033) — unspellable in-subset, so the region declines
        // instead of verdicting.
        let binder = binder_with(&[("uv", span(0, 10)), ("a", span(40, 60))]);
        let decls = [unknown_decl("uv", 0, 10, None)];
        let uses = [narrowing_use("a", 40, 60, "string", "uv", 58, 59)];
        let guards = [guard(
            "uv",
            "object",
            false,
            false,
            guard_spans(20, 70, None, 10, 70),
        )];
        let report = narrow_report(&decls, &uses, &guards, &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1]
                .reason
                .contains("narrowable primitive"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn narrowing_genuinely_unknown_keeps_legacy_note() {
        // No annotation and no literal init: genuinely unknown, never
        // verdicts — the declaration notes, and uses of it keep the legacy
        // non-literal note (tsc infers `unknown` and stays clean: a pinned
        // oracle-clean divergence).
        let binder = binder_with(&[
            ("uv", span(0, 10)),
            ("g", span(20, 30)),
            ("h", span(40, 50)),
        ]);
        let decls = [
            unknown_decl("uv", 0, 10, None),
            ConstDecl {
                name: "g".to_owned(),
                span: span(20, 30),
                scope: 0,
                symbol: None,
                kind: DeclKind::Const,
                annotation: None,
                init: Some(InitKind::NonLiteral),
                init_object: None,
                init_array: None,
                cast: None,
            },
        ];
        let uses = [narrowing_use("h", 40, 50, "string", "g", 48, 49)];
        let report = narrow_report(&decls, &uses, &[], &[], &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 3);
        assert!(
            report.unsupported[1].reason.contains("no annotation"),
            "reason: {}",
            report.unsupported[1].reason
        );
        assert_eq!(
            report.unsupported[2].reason,
            "non-literal initializer is outside the subset"
        );
    }

    #[test]
    fn narrowing_non_union_decls_delegate_unchanged() {
        // Primitive and object declarations route to `check_one` verbatim.
        let binder = binder_with(&[("a", span(0, 10)), ("p", span(11, 21))]);
        let decls = [
            decl("a", 0, 10, "number", InitKind::String),
            object_decl(
                "p",
                11,
                21,
                "{ x: number }",
                vec![("x", ObjectMemberKind::Number)],
            ),
        ];
        let report = narrow_report(&decls, &[], &[], &[], &binder);
        assert!(report.unsupported.is_empty());
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
    }

    fn generic_param(annotation: Option<&str>) -> FunctionParam {
        FunctionParam {
            name: "x".to_owned(),
            annotated: annotation.is_some(),
            annotation: annotation.map(str::to_owned),
            optional: false,
            is_rest: false,
        }
    }

    fn generic_param_named(name: &str, annotation: Option<&str>) -> FunctionParam {
        FunctionParam {
            name: name.to_owned(),
            annotated: annotation.is_some(),
            annotation: annotation.map(str::to_owned),
            optional: false,
            is_rest: false,
        }
    }

    fn unbounded(count: usize) -> Vec<TypeParamBound> {
        vec![
            TypeParamBound {
                constraint: None,
                default: None
            };
            count
        ]
    }

    fn generic_decl_named(
        name: &str,
        lo: u32,
        hi: u32,
        t_params: &[&str],
        param_ann: Option<&str>,
        ret_ann: Option<&str>,
        body: FunctionBody,
    ) -> GenericDecl {
        GenericDecl {
            decl: FunctionDecl {
                name: name.to_owned(),
                span: span(lo, hi),
                scope: 0,
                symbol: None,
                params: vec![generic_param(param_ann)],
                params_complex: false,
                is_async: false,
                has_type_params: false,
                return_annotation: ret_ann.map(str::to_owned),
                body,
            },
            type_params: t_params.iter().map(|param| (*param).to_owned()).collect(),
            type_params_complex: false,
            bounds: unbounded(t_params.len()),
        }
    }

    /// The canonical identity declaration: `function id<T>(x: T): T` with a
    /// pass-through body (non-literal, so the declaration declines while
    /// calls still check — P014 precedent).
    fn identity_decl(lo: u32, hi: u32) -> GenericDecl {
        generic_decl_named(
            "id",
            lo,
            hi,
            &["T"],
            Some("T"),
            Some("T"),
            FunctionBody::SingleReturn(FunctionReturn {
                kind: Some(InitKind::NonLiteral),
                init_object: None,
                init_array: None,
                cast: None,
            }),
        )
    }

    fn generic_call_args(
        callee: &str,
        callee_lo: u32,
        callee_hi: u32,
        args: Vec<(InitKind, u32, u32)>,
        explicit: Option<Vec<&str>>,
    ) -> GenericCall {
        GenericCall {
            call: CallSite {
                callee: callee.to_owned(),
                callee_span: span(callee_lo, callee_hi),
                span: span(callee_lo, callee_hi + 2),
                args: args
                    .into_iter()
                    .map(|(kind, lo, hi)| CallArg {
                        kind,
                        span: span(lo, hi),
                        cast: None,
                    })
                    .collect(),
            },
            explicit_args: explicit.map(|texts| texts.into_iter().map(str::to_owned).collect()),
        }
    }

    fn generics_report(
        decls: &[GenericDecl],
        calls: &[GenericCall],
        binder: &Binder,
    ) -> FileReport {
        check_generics(FILE, decls, calls, binder)
    }

    #[test]
    fn generic_explicit_correct_binds_silently() {
        // `id<number>(1)`: the argument matches the instantiation, so no
        // diagnostic. The pass-through body still declines (one note).
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args("id", 30, 32, args, Some(vec!["number"]))];
        let report = generics_report(&decls, &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("non-literal return"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn generic_explicit_wrong_is_ts2345() {
        // `id<number>("oops")`: the oracle's TS2345 at the argument.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let args = vec![(InitKind::String, 40, 46)];
        let calls = [generic_call_args("id", 30, 32, args, Some(vec!["number"]))];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        assert_eq!(report.diagnostics[0].span, span(40, 46));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_explicit_count_is_ts2558() {
        // `id<number, string>(1)`: the oracle's TS2558 at the callee.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let calls = [generic_call_args(
            "id",
            30,
            32,
            vec![(InitKind::Number, 40, 41)],
            Some(vec!["number", "string"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_TYPE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 1 type arguments, but got 2."
        );
        assert_eq!(report.diagnostics[0].span, span(30, 32));
    }

    #[test]
    fn generic_explicit_unknown_is_ts2304() {
        // `id<Nope>(1)`: the oracle's TS2304 (callee-anchored: no
        // type-argument spans exist in facts).
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args("id", 30, 32, args, Some(vec!["Nope"]))];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
    }

    #[test]
    fn generic_explicit_union_declines() {
        // `id<number | string>(1)` is clean in tsc but unspellable here:
        // the call declines (plus the body's own note).
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let calls = [generic_call_args(
            "id",
            30,
            32,
            vec![(InitKind::Number, 40, 41)],
            Some(vec!["number | string"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("type argument"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn generic_inferred_correct_binds_silently() {
        // `id(1)`: T binds `number` from the literal; the check is vacuous
        // by construction, so only the body note remains.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args("id", 30, 32, args, None)];
        let report = generics_report(&decls, &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_literal_body_diagnoses_against_t() {
        // `return "s"` against `T`: the oracle's TS2322, call-independent
        // (tsc checks generic bodies against `T` directly). The `f(1)` call
        // still infers cleanly beside it.
        let binder = binder_with(&[("f", span(0, 20))]);
        let decls = [generic_decl_named(
            "f",
            0,
            20,
            &["T"],
            Some("T"),
            Some("T"),
            FunctionBody::SingleReturn(FunctionReturn {
                kind: Some(InitKind::String),
                init_object: None,
                init_array: None,
                cast: None,
            }),
        )];
        let calls = [generic_call_args(
            "f",
            30,
            31,
            vec![(InitKind::Number, 40, 41)],
            None,
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'T'."
        );
        assert_eq!(report.diagnostics[0].span, span(0, 20));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn generic_object_body_spells_against_t() {
        // `return { v: 1 }` against `T`: the oracle's `{ v: number; }`
        // spelling (probed tsc 7.0.2).
        let binder = binder_with(&[("f", span(0, 20))]);
        let decls = [generic_decl_named(
            "f",
            0,
            20,
            &["T"],
            Some("T"),
            Some("T"),
            FunctionBody::SingleReturn(FunctionReturn {
                kind: None,
                init_object: Some(ObjectInit {
                    members: vec![ObjectMemberInit {
                        name: "v".to_owned(),
                        kind: ObjectMemberKind::Number,
                    }],
                    fresh: true,
                }),
                init_array: None,
                cast: None,
            }),
        )];
        let report = generics_report(&decls, &[], &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '{ v: number; }' is not assignable to type 'T'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn generic_custom_param_name_spells_in_messages() {
        // `U` behaves exactly like `T`, including in message spellings.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [generic_decl_named(
            "id",
            0,
            20,
            &["U"],
            Some("U"),
            Some("U"),
            FunctionBody::SingleReturn(FunctionReturn {
                kind: Some(InitKind::Number),
                init_object: None,
                init_array: None,
                cast: None,
            }),
        )];
        let report = generics_report(&decls, &[], &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' is not assignable to type 'U'."
        );
    }

    #[test]
    fn generic_inference_failure_declines() {
        // `id(u)` over an identifier: tsc binds from the identifier's type,
        // but the subset has no expression facts — one call note (plus the
        // body's own note), never silent.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let calls = [generic_call_args(
            "id",
            30,
            32,
            vec![(InitKind::NonLiteral, 40, 41)],
            None,
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("cannot infer"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    /// The canonical pair declaration: `function pair<T, U>(x: T, y: U): T`
    /// with a pass-through body (non-literal, so the declaration declines
    /// while calls still check — P014 precedent).
    fn pair_decl(lo: u32, hi: u32) -> GenericDecl {
        GenericDecl {
            decl: FunctionDecl {
                name: "pair".to_owned(),
                span: span(lo, hi),
                scope: 0,
                symbol: None,
                params: vec![
                    generic_param_named("x", Some("T")),
                    generic_param_named("y", Some("U")),
                ],
                params_complex: false,
                is_async: false,
                has_type_params: false,
                return_annotation: Some("T".to_owned()),
                body: FunctionBody::SingleReturn(FunctionReturn {
                    kind: Some(InitKind::NonLiteral),
                    init_object: None,
                    init_array: None,
                    cast: None,
                }),
            },
            type_params: vec!["T".to_owned(), "U".to_owned()],
            type_params_complex: false,
            bounds: unbounded(2),
        }
    }

    #[test]
    fn generic_multi_param_inferred_correct_binds_silently() {
        // `pair(1, "s")`: each parameter binds from its own argument, so no
        // diagnostic. The pass-through body still declines (one note).
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [generic_call_args("pair", 30, 34, args, None)];
        let report = generics_report(&decls, &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("non-literal return"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn generic_multi_param_explicit_wrong_first_is_ts2345() {
        // `pair<number, string>(true, "s")`: the oracle's TS2345 at the
        // FIRST mismatched argument only.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Boolean, 40, 44), (InitKind::String, 46, 50)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["number", "string"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'boolean' is not assignable to parameter of type 'number'."
        );
        assert_eq!(report.diagnostics[0].span, span(40, 44));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_explicit_wrong_second_is_ts2345() {
        // `pair<number, string>(1, true)`: the oracle's TS2345 at the
        // second argument (the first matches, so only the second fires).
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41), (InitKind::Boolean, 43, 47)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["number", "string"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'boolean' is not assignable to parameter of type 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(43, 47));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_explicit_count_is_ts2558() {
        // `pair<number>(1, "s")` and `pair<number, string, boolean>(1,
        // "s")`: the oracle's TS2558 at the callee in both directions.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = || vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [
            generic_call_args("pair", 30, 34, args(), Some(vec!["number"])),
            generic_call_args(
                "pair",
                50,
                54,
                args(),
                Some(vec!["number", "string", "boolean"]),
            ),
        ];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert!(report
            .diagnostics
            .iter()
            .all(|diag| diag.code == CODE_TYPE_ARITY));
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 type arguments, but got 1."
        );
        assert_eq!(report.diagnostics[0].span, span(30, 34));
        assert_eq!(
            report.diagnostics[1].message,
            "Expected 2 type arguments, but got 3."
        );
        assert_eq!(report.diagnostics[1].span, span(50, 54));
    }

    #[test]
    fn generic_multi_param_type_arity_beats_value_arity() {
        // `pair<number>(1)`: both arities miss, but the oracle reports only
        // TS2558 — explicit type-argument arity gates first.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["number"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_TYPE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 type arguments, but got 1."
        );
    }

    #[test]
    fn generic_multi_param_value_arity_still_resolves() {
        // `pair<Nope, string>(1)`: the oracle pairs TS2554 with TS2304 —
        // value arity never suppresses name resolution.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["Nope", "string"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 arguments, but got 1."
        );
        assert_eq!(report.diagnostics[1].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[1].message, "Cannot find name 'Nope'.");
    }

    #[test]
    fn generic_multi_param_value_arity_skips_arg_checks() {
        // `pair<string, number>(1)`: the oracle reports only TS2554 — the
        // prefix argument never checks once arity misses.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["string", "number"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 2 arguments, but got 1."
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_both_unknown_report_twice() {
        // `pair<Nope, AlsoNope>(1, "s")`: the oracle reports one TS2304 per
        // name — resolution never stops at the first miss.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["Nope", "AlsoNope"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert!(report
            .diagnostics
            .iter()
            .all(|diag| diag.code == CODE_UNKNOWN_ANNOTATION));
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
        assert_eq!(
            report.diagnostics[1].message,
            "Cannot find name 'AlsoNope'."
        );
    }

    #[test]
    fn generic_multi_param_constrained_inferred_wrong_first() {
        // `cpair(1, "s")` over `<T extends string, U>`: the oracle's TS2345
        // at the first argument against the constraint spelling.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.bounds[0].constraint = Some("string".to_owned());
        let args = vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [generic_call_args("pair", 30, 34, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(40, 41));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_constrained_inferred_wrong_second() {
        // `("s", true)` over `<T, U extends number>`: the oracle's TS2345
        // at the second argument (the first binds cleanly).
        let binder = binder_with(&[("pair", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.bounds[1].constraint = Some("number".to_owned());
        let args = vec![(InitKind::String, 40, 44), (InitKind::Boolean, 46, 50)];
        let calls = [generic_call_args("pair", 30, 34, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'boolean' is not assignable to parameter of type 'number'."
        );
        assert_eq!(report.diagnostics[0].span, span(46, 50));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_both_violate_reports_first_ts2344() {
        // `cpair<number, boolean>("s", true)` over `<T extends string, U
        // extends number>`: the oracle reports only the first TS2344 —
        // satisfaction stops at the first violation.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.bounds[0].constraint = Some("string".to_owned());
        decl.bounds[1].constraint = Some("number".to_owned());
        let args = vec![(InitKind::String, 40, 44), (InitKind::Boolean, 46, 50)];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            args,
            Some(vec!["number", "boolean"]),
        )];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_CONSTRAINT);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' does not satisfy the constraint 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(30, 34));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_default_fills_second_position() {
        // `mix(1, u)` over `<T, U = number>`: no literal candidate for `U`,
        // so its default binds and the per-argument skip stays silent.
        let binder = binder_with(&[("mix", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.decl.name = "mix".to_owned();
        decl.bounds[1].default = Some("number".to_owned());
        let args = vec![(InitKind::Number, 40, 41), (InitKind::NonLiteral, 43, 44)];
        let calls = [generic_call_args("mix", 30, 33, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_inference_failure_names_position() {
        // `pair(1, u)` with no defaults: tsc binds from the identifier's
        // type (clean) while the subset declines naming `U` (plus the body
        // note), never silent.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41), (InitKind::NonLiteral, 43, 44)];
        let calls = [generic_call_args("pair", 30, 34, args, None)];
        let report = generics_report(&decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("cannot infer 'U'"),
            "reason: {}",
            report.unsupported[1].reason
        );
    }

    #[test]
    fn generic_multi_param_partial_explicit_uses_default() {
        // `mix<string>("s", 1)` over `<T, U = number>`: the missing
        // trailing type argument fills from its default, so both positions
        // check silently.
        let binder = binder_with(&[("mix", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.decl.name = "mix".to_owned();
        decl.bounds[1].default = Some("number".to_owned());
        let args = vec![(InitKind::String, 40, 44), (InitKind::Number, 46, 47)];
        let calls = [generic_call_args("mix", 30, 33, args, Some(vec!["string"]))];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_multi_param_range_spelling_with_defaults() {
        // `mix<string, number, boolean>(1, 2)` over `<T, U = number>`: the
        // oracle's TS2558 spells the admitted range at the callee.
        let binder = binder_with(&[("mix", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.decl.name = "mix".to_owned();
        decl.bounds[1].default = Some("number".to_owned());
        let args = vec![(InitKind::Number, 40, 41), (InitKind::Number, 43, 44)];
        let calls = [generic_call_args(
            "mix",
            30,
            33,
            args,
            Some(vec!["string", "number", "boolean"]),
        )];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_TYPE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 1-2 type arguments, but got 3."
        );
        assert_eq!(report.diagnostics[0].span, span(30, 33));
    }

    #[test]
    fn generic_triple_param_inferred_correct_binds_silently() {
        // `tri(1, "s", true)`: three independent positions bind cleanly.
        let binder = binder_with(&[("tri", span(0, 20))]);
        let decl = GenericDecl {
            decl: FunctionDecl {
                name: "tri".to_owned(),
                span: span(0, 20),
                scope: 0,
                symbol: None,
                params: vec![
                    generic_param_named("x", Some("A")),
                    generic_param_named("y", Some("B")),
                    generic_param_named("z", Some("C")),
                ],
                params_complex: false,
                is_async: false,
                has_type_params: false,
                return_annotation: Some("A".to_owned()),
                body: FunctionBody::SingleReturn(FunctionReturn {
                    kind: Some(InitKind::NonLiteral),
                    init_object: None,
                    init_array: None,
                    cast: None,
                }),
            },
            type_params: vec!["A".to_owned(), "B".to_owned(), "C".to_owned()],
            type_params_complex: false,
            bounds: unbounded(3),
        };
        let args = vec![
            (InitKind::Number, 40, 41),
            (InitKind::String, 43, 47),
            (InitKind::Boolean, 49, 53),
        ];
        let calls = [generic_call_args("tri", 30, 33, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_four_params_decline() {
        // Four type parameters stay outside the admitted two-to-three.
        let binder = binder_with(&[("f", span(0, 20))]);
        let decls = [generic_decl_named(
            "f",
            0,
            20,
            &["A", "B", "C", "D"],
            Some("A"),
            Some("A"),
            FunctionBody::Complex,
        )];
        let report = generics_report(&decls, &[], &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("multiple type parameters"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn generic_nontrailing_default_declines() {
        // `<T = string, U>`: tsc spells TS2706, so the subset declines
        // instead of instantiating a list explicit arguments could never
        // fill positionally.
        let binder = binder_with(&[("f", span(0, 20))]);
        let mut decl = generic_decl_named(
            "f",
            0,
            20,
            &["T", "U"],
            Some("T"),
            Some("T"),
            FunctionBody::Complex,
        );
        decl.decl.params.push(generic_param_named("y", Some("U")));
        decl.bounds[0].default = Some("string".to_owned());
        let report = generics_report(&[decl], &[], &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("may not follow optional"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn generic_return_u_admits() {
        // `: U` returns check exactly like `: T`: the body diagnoses
        // against `U` while calls instantiate both positions.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.decl.return_annotation = Some("U".to_owned());
        let args = vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [generic_call_args("pair", 30, 34, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_duplicate_names_check_per_position() {
        // `(x: T, y: T)` shares one slot: each literal verifies against its
        // own binding, so both stay silent. Tsc instead binds the literal
        // type `1`, then reports TS2345 on `"s"` — literal-type inference
        // is outside the subset (pinned oracle-error divergence).
        let binder = binder_with(&[("f", span(0, 20))]);
        let mut decl = pair_decl(0, 20);
        decl.decl.name = "f".to_owned();
        decl.decl.params[1].annotation = Some("T".to_owned());
        let args = vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [generic_call_args("f", 30, 31, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_empty_explicit_declines() {
        // `pair<>(1, "s")`: tsc spells TS1099 (grammar error), so the
        // subset declines instead of verdicting.
        let binder = binder_with(&[("pair", span(0, 20))]);
        let decls = [pair_decl(0, 20)];
        let args = vec![(InitKind::Number, 40, 41), (InitKind::String, 43, 47)];
        let calls = [generic_call_args("pair", 30, 34, args, Some(vec![]))];
        let report = generics_report(&decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 2);
        assert!(
            report.unsupported[1].reason.contains("empty type argument"),
            "reason: {:?}",
            report.unsupported
        );
    }

    #[test]
    fn generic_single_both_wrong_reports_type_arity() {
        // `id<number, string>()`: both arities miss, but the oracle reports
        // only TS2558 (probed tsc 7.0.2 P036) — explicit type-argument
        // arity gates first, single parameters included.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let calls = [generic_call_args(
            "id",
            30,
            32,
            vec![],
            Some(vec!["number", "string"]),
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_TYPE_ARITY);
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 1 type arguments, but got 2."
        );
    }

    #[test]
    fn generic_complex_type_params_decline() {
        // `in`/`out`/`const` modifiers arrive as one flag: one reason.
        // (Constraints and defaults are facts now — see the bound tests.)
        let binder = binder_with(&[("id", span(0, 20))]);
        let mut decl = identity_decl(0, 20);
        decl.type_params_complex = true;
        let report = generics_report(&[decl], &[], &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("modifier"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    /// The canonical bounded declaration: `function name<T extends C = D>(x:
    /// T): T` with a pass-through body (non-literal, so the declaration
    /// declines while calls still check — P014 precedent).
    fn bounded_decl(
        name: &str,
        lo: u32,
        hi: u32,
        constraint: Option<&str>,
        default: Option<&str>,
    ) -> GenericDecl {
        let mut decl = generic_decl_named(
            name,
            lo,
            hi,
            &["T"],
            Some("T"),
            Some("T"),
            FunctionBody::SingleReturn(FunctionReturn {
                kind: Some(InitKind::NonLiteral),
                init_object: None,
                init_array: None,
                cast: None,
            }),
        );
        decl.bounds[0].constraint = constraint.map(str::to_owned);
        decl.bounds[0].default = default.map(str::to_owned);
        decl
    }

    #[test]
    fn generic_constrained_inferred_correct_binds_silently() {
        // `idc("s")` over `<T extends string>`: the inferred `string`
        // satisfies the constraint, so only the body note remains.
        let binder = binder_with(&[("idc", span(0, 20))]);
        let decl = bounded_decl("idc", 0, 20, Some("string"), None);
        let args = vec![(InitKind::String, 40, 44)];
        let calls = [generic_call_args("idc", 30, 33, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_constrained_inferred_wrong_is_ts2345() {
        // `idc(1)` over `<T extends string>`: the oracle's TS2345 at the
        // argument against the constraint spelling (never TS2344).
        let binder = binder_with(&[("idc", span(0, 20))]);
        let decl = bounded_decl("idc", 0, 20, Some("string"), None);
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args("idc", 30, 33, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(40, 41));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_constrained_explicit_violation_is_ts2344() {
        // `idc<number>("s")`: the oracle's TS2344 (callee-anchored: no
        // type-argument spans exist in facts — the TS2304/TS2558 fold).
        let binder = binder_with(&[("idc", span(0, 20))]);
        let decl = bounded_decl("idc", 0, 20, Some("string"), None);
        let args = vec![(InitKind::String, 40, 44)];
        let calls = [generic_call_args("idc", 30, 33, args, Some(vec!["number"]))];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_CONSTRAINT);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' does not satisfy the constraint 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(30, 33));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_constrained_explicit_satisfies_then_arg_checks() {
        // `idc<string>("s")` is silent while `idc<string>(1)` reports
        // TS2345: satisfaction beats argument checks, never replaces them.
        let binder = binder_with(&[("idc", span(0, 20))]);
        let decl = bounded_decl("idc", 0, 20, Some("string"), None);
        let calls = [
            generic_call_args(
                "idc",
                30,
                33,
                vec![(InitKind::String, 40, 44)],
                Some(vec!["string"]),
            ),
            generic_call_args(
                "idc",
                50,
                53,
                vec![(InitKind::Number, 60, 61)],
                Some(vec!["string"]),
            ),
        ];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(60, 61));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_constrained_explicit_unknown_is_ts2304() {
        // `idc<Nope>(1)`: name resolution beats satisfaction — TS2304, even
        // against a declared constraint.
        let binder = binder_with(&[("idc", span(0, 20))]);
        let decl = bounded_decl("idc", 0, 20, Some("string"), None);
        let args = vec![(InitKind::Number, 40, 41)];
        let calls = [generic_call_args("idc", 30, 33, args, Some(vec!["Nope"]))];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
    }

    #[test]
    fn generic_defaulted_fills_missing_inference() {
        // `idd(u)` over `<T = number>`: no literal candidate, so the
        // default binds and the per-argument skip stays silent (the oracle
        // binds from the identifier's type — clean either way).
        let binder = binder_with(&[("idd", span(0, 20))]);
        let decl = bounded_decl("idd", 0, 20, None, Some("number"));
        let args = vec![(InitKind::NonLiteral, 40, 41)];
        let calls = [generic_call_args("idd", 30, 33, args, None)];
        let report = generics_report(&[decl], &calls, &binder);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_defaulted_inferred_and_override_check() {
        // `idd(1)` prefers inference silently; `idd<string>(1)` overrides
        // the default and reports TS2345.
        let binder = binder_with(&[("idd", span(0, 20))]);
        let decl = bounded_decl("idd", 0, 20, None, Some("number"));
        let calls = [
            generic_call_args("idd", 30, 33, vec![(InitKind::Number, 40, 41)], None),
            generic_call_args(
                "idd",
                50,
                53,
                vec![(InitKind::Number, 60, 61)],
                Some(vec!["string"]),
            ),
        ];
        let report = generics_report(&[decl], &calls, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_ARG_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        assert_eq!(report.diagnostics[0].span, span(60, 61));
        assert_eq!(report.unsupported.len(), 1);
    }

    #[test]
    fn generic_non_primitive_bounds_decline() {
        // Union/keyof constraints and object defaults decline with distinct
        // reasons; their calls skip (the declaration note covers them).
        let binder = binder_with(&[("f", span(0, 20)), ("g", span(21, 41)), ("h", span(42, 62))]);
        let decls = [
            bounded_decl("f", 0, 20, Some("string | number"), None),
            bounded_decl("g", 21, 41, Some("keyof T"), None),
            bounded_decl("h", 42, 62, None, Some("{ v: number }")),
        ];
        let calls = [generic_call_args(
            "f",
            70,
            71,
            vec![(InitKind::Number, 72, 73)],
            None,
        )];
        let report = generics_report(&decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 3);
        assert!(
            report.unsupported[0].reason.contains("union constraint"),
            "reason: {}",
            report.unsupported[0].reason
        );
        assert!(
            report.unsupported[1].reason.contains("keyof constraint"),
            "reason: {}",
            report.unsupported[1].reason
        );
        assert!(
            report.unsupported[2].reason.contains("object default"),
            "reason: {}",
            report.unsupported[2].reason
        );
    }

    #[test]
    fn generic_advanced_t_positions_decline() {
        // `keyof` parameters, conditional and mapped returns, and `infer`
        // bounds each decline with a distinct reason.
        let binder = binder_with(&[
            ("f", span(0, 20)),
            ("g", span(21, 41)),
            ("h", span(42, 62)),
            ("k", span(63, 83)),
        ]);
        let body = || {
            FunctionBody::SingleReturn(FunctionReturn {
                kind: Some(InitKind::NonLiteral),
                init_object: None,
                init_array: None,
                cast: None,
            })
        };
        let mut infer_named = generic_decl_named("k", 63, 83, &["T"], Some("T"), Some("T"), body());
        infer_named.bounds[0].constraint = Some("infer U".to_owned());
        let decls = [
            generic_decl_named("f", 0, 20, &["T"], Some("keyof T"), Some("T"), body()),
            generic_decl_named(
                "g",
                21,
                41,
                &["T"],
                Some("T"),
                Some("T extends string ? string : number"),
                body(),
            ),
            generic_decl_named(
                "h",
                42,
                62,
                &["T"],
                Some("T"),
                Some("{ [K in keyof T]: T[K] }"),
                body(),
            ),
            infer_named,
        ];
        let report = generics_report(&decls, &[], &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 4);
        assert!(
            report.unsupported[0].reason.contains("keyof parameter"),
            "reason: {}",
            report.unsupported[0].reason
        );
        assert!(
            report.unsupported[1].reason.contains("conditional return"),
            "reason: {}",
            report.unsupported[1].reason
        );
        assert!(
            report.unsupported[2].reason.contains("mapped return"),
            "reason: {}",
            report.unsupported[2].reason
        );
        assert!(
            report.unsupported[3].reason.contains("infer constraint"),
            "reason: {}",
            report.unsupported[3].reason
        );
    }

    #[test]
    fn generic_nested_t_positions_decline() {
        // `T` outside a bare position (union param, object param, object
        // return, primitive param) declines with a distinct reason each.
        let binder = binder_with(&[
            ("f", span(0, 20)),
            ("g", span(21, 41)),
            ("h", span(42, 62)),
            ("k", span(63, 83)),
        ]);
        let body = || {
            FunctionBody::SingleReturn(FunctionReturn {
                kind: Some(InitKind::NonLiteral),
                init_object: None,
                init_array: None,
                cast: None,
            })
        };
        let decls = [
            generic_decl_named("f", 0, 20, &["T"], Some("T | string"), Some("T"), body()),
            generic_decl_named("g", 21, 41, &["T"], Some("{ v: T }"), Some("T"), body()),
            generic_decl_named("h", 42, 62, &["T"], Some("T"), Some("{ v: T }"), body()),
            generic_decl_named("k", 63, 83, &["T"], Some("number"), Some("T"), body()),
        ];
        let report = generics_report(&decls, &[], &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 4);
        assert!(
            report.unsupported[0].reason.contains("union parameter"),
            "reason: {}",
            report.unsupported[0].reason
        );
        assert!(
            report.unsupported[1].reason.contains("object parameter"),
            "reason: {}",
            report.unsupported[1].reason
        );
        assert!(
            report.unsupported[2].reason.contains("object return"),
            "reason: {}",
            report.unsupported[2].reason
        );
        assert!(
            report.unsupported[3].reason.contains("bare type parameter"),
            "reason: {}",
            report.unsupported[3].reason
        );
    }

    #[test]
    fn generic_missing_return_and_arity_decline() {
        // No return annotation declines; zero-arg and two-arg calls report
        // TS2554 at the oracle's spans.
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [generic_decl_named(
            "id",
            0,
            20,
            &["T"],
            Some("T"),
            None,
            FunctionBody::Complex,
        )];
        let calls = [
            generic_call_args("id", 30, 32, vec![], Some(vec!["number"])),
            generic_call_args(
                "id",
                50,
                52,
                vec![(InitKind::Number, 60, 61), (InitKind::Number, 63, 64)],
                None,
            ),
        ];
        let report = generics_report(&decls, &calls, &binder);
        // The declaration declines (no return annotation), so both calls
        // skip silently: arity never runs against a declined declaration.
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("no return annotation"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn generic_arity_reports_on_checkable_decls() {
        // Arity runs once the declaration gates pass: too-few anchors at
        // the callee, too-many at the first excess argument (P014 mirrors).
        let binder = binder_with(&[("id", span(0, 20))]);
        let decls = [identity_decl(0, 20)];
        let calls = [
            generic_call_args("id", 30, 32, vec![], Some(vec!["number"])),
            generic_call_args(
                "id",
                50,
                52,
                vec![(InitKind::Number, 60, 61), (InitKind::Number, 63, 64)],
                None,
            ),
        ];
        let report = generics_report(&decls, &calls, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert!(report
            .diagnostics
            .iter()
            .all(|diag| diag.code == CODE_ARITY));
        assert_eq!(report.diagnostics[0].span, span(30, 32));
        assert_eq!(report.diagnostics[1].span, span(63, 64));
        assert_eq!(
            report.diagnostics[0].message,
            "Expected 1 arguments, but got 0."
        );
        assert_eq!(
            report.diagnostics[1].message,
            "Expected 1 arguments, but got 2."
        );
    }

    #[test]
    fn generic_overloads_and_undeclared_mirror_calls() {
        // Overloads decline per call; unresolved-tracked callees skip
        // silently (P014 precedent, never double-diagnosed).
        let binder = calls_binder(&[("id", span(0, 20)), ("id", span(21, 41))], &["missing"]);
        let decls = [identity_decl(0, 20), identity_decl(21, 41)];
        let calls = [
            generic_call_args("id", 50, 52, vec![(InitKind::Number, 60, 61)], None),
            generic_call_args("missing", 70, 77, vec![(InitKind::Number, 78, 79)], None),
        ];
        let report = generics_report(&decls, &calls, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 3);
        assert!(report
            .unsupported
            .iter()
            .any(|note| note.reason.contains("multiple declarations")));
    }

    #[test]
    fn generic_occurrence_nodes_stay_disjoint() {
        // Inference keys must never alias const or function memo nodes when
        // checkers share a file.
        assert_ne!(generic_occurrence_node(0), occurrence_node(0));
        assert_ne!(generic_occurrence_node(0), function_occurrence_node(0));
        assert_ne!(generic_occurrence_node(3), generic_occurrence_node(4));
    }

    #[test]
    fn generic_reports_sort_deterministically() {
        // Scrambled declaration order still verdicts in span order.
        let binder = binder_with(&[("b", span(40, 60)), ("a", span(0, 20))]);
        let decls = [identity_decl(40, 60), identity_decl(0, 20)];
        let report = generics_report(&decls, &[], &binder);
        assert_eq!(report.unsupported.len(), 2);
        let los: Vec<u32> = report.unsupported.iter().map(|note| note.span.lo).collect();
        assert_eq!(los, [0, 40]);
        let repeat = generics_report(&decls, &[], &binder);
        assert_eq!(report, repeat);
    }

    fn enum_member_named(name: &str, value: EnumMemberValue) -> EnumMember {
        EnumMember {
            name: name.to_owned(),
            value,
            span: span(0, 1),
        }
    }

    /// One enum shape bound to `binder`, mirroring the e2e driver contract.
    fn check_enum_shape_for(
        binder: &Binder,
        name: &str,
        scope: u32,
        members: Vec<EnumMember>,
    ) -> EnumShape {
        EnumShape {
            name: name.to_owned(),
            scope,
            symbol: binder.resolve(FILE, scope, name),
            span: span(0, 1),
            members,
            is_const: false,
            declared: false,
            exported: true,
        }
    }

    fn namespace_shape_for(
        binder: &Binder,
        name: &str,
        scope: u32,
        body_scope: u32,
        exported: bool,
        exported_members: Vec<&str>,
    ) -> NamespaceShape {
        NamespaceShape {
            name: name.to_owned(),
            scope,
            symbol: binder.resolve(FILE, scope, name),
            span: span(0, 1),
            body_scope,
            declared: false,
            exported,
            exported_members: exported_members.into_iter().map(str::to_owned).collect(),
        }
    }

    fn enum_decl_for(
        name: &str,
        lo: u32,
        hi: u32,
        annotation: &str,
        init: InitKind,
        text: Option<&str>,
    ) -> EnumDecl {
        EnumDecl {
            decl: ConstDecl {
                name: name.to_owned(),
                span: span(lo, hi),
                scope: 0,
                symbol: None,
                kind: DeclKind::Const,
                annotation: Some(annotation.to_owned()),
                init: Some(init),
                init_object: None,
                init_array: None,
                cast: None,
            },
            init_text: text.map(str::to_owned),
            cross_file_deps: Vec::new(),
        }
    }

    /// A binder with namespace body scopes: scope 1 hangs off root 0, and
    /// scope 2 hangs off scope 1 (two-level nesting).
    fn enum_binder(declared: &[(&str, u32, Span)], unresolved: &[&str]) -> Binder {
        let mut binder = Binder::new();
        let symbols: Vec<SymbolInput> = declared
            .iter()
            .map(|(name, scope, decl_span)| SymbolInput {
                scope: *scope,
                name: (*name).to_owned(),
                span: *decl_span,
                flags: 0,
            })
            .collect();
        let missing: Vec<UnresolvedInput> = unresolved
            .iter()
            .map(|name| UnresolvedInput {
                name: (*name).to_owned(),
                count: 1,
            })
            .collect();
        binder.build_file(
            FILE,
            &[
                ScopeInput {
                    index: 0,
                    parent: u32::MAX,
                },
                ScopeInput {
                    index: 1,
                    parent: 0,
                },
                ScopeInput {
                    index: 2,
                    parent: 1,
                },
            ],
            &symbols,
            &missing,
        );
        binder
    }

    fn color_shape(binder: &Binder) -> EnumShape {
        check_enum_shape_for(
            binder,
            "Color",
            0,
            vec![
                enum_member_named("Red", EnumMemberValue::Number(0.0)),
                enum_member_named("Green", EnumMemberValue::Number(1.0)),
                enum_member_named("Blue", EnumMemberValue::Number(2.0)),
            ],
        )
    }

    fn enums_report(decls: &[EnumDecl], input: &EnumInput<'_>, binder: &Binder) -> FileReport {
        let mut db = QueryDb::new();
        check_enums(FILE, decls, input, binder, &mut db)
    }

    #[test]
    fn enum_numeric_literals_check_membership_by_value() {
        let binder = binder_with(&[
            ("Color", span(0, 5)),
            ("a", span(6, 16)),
            ("b", span(17, 27)),
        ]);
        let shape = color_shape(&binder);
        let input = EnumInput {
            enums: &[shape],
            interfaces: &[],
            namespaces: &[],
        };
        let decls = [
            enum_decl_for("a", 6, 16, "Color", InitKind::Number, Some("1")),
            enum_decl_for("b", 17, 27, "Color", InitKind::Number, Some("5")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '5' is not assignable to type 'Color'."
        );
        assert_eq!(report.diagnostics[0].span, span(17, 27));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn enum_string_literals_never_match() {
        let binder = binder_with(&[("Str", span(0, 3)), ("g", span(4, 14)), ("t", span(15, 25))]);
        let shape = check_enum_shape_for(
            &binder,
            "Str",
            0,
            vec![
                enum_member_named("A", EnumMemberValue::String("a".to_owned())),
                enum_member_named("B", EnumMemberValue::String("b".to_owned())),
            ],
        );
        let input = EnumInput {
            enums: &[shape],
            interfaces: &[],
            namespaces: &[],
        };
        let decls = [
            enum_decl_for("g", 4, 14, "Str", InitKind::String, Some("\"a\"")),
            enum_decl_for("t", 15, 25, "Str", InitKind::Boolean, Some("true")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '\"a\"' is not assignable to type 'Str'."
        );
        assert_eq!(
            report.diagnostics[1].message,
            "Type 'true' is not assignable to type 'Str'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn enum_spellings_parse_and_render_values() {
        assert_eq!(parse_enum_number("5"), Some(5.0));
        assert_eq!(parse_enum_number("  2.5  "), Some(2.5));
        assert_eq!(parse_enum_number("1_0"), Some(10.0));
        assert_eq!(parse_enum_number("0x11"), None);
        assert_eq!(parse_enum_number(""), None);
        assert_eq!(spell_number(5.0), "5");
        assert_eq!(spell_number(2.5), "2.5");
        assert_eq!(spell_number(0.0), "0");
    }

    #[test]
    fn enum_computed_ambient_and_merged_decline() {
        let binder = binder_with(&[
            ("Comp", span(0, 4)),
            ("Amb", span(5, 8)),
            ("Dup", span(9, 12)),
            ("a", span(13, 23)),
            ("b", span(24, 34)),
            ("c", span(35, 45)),
        ]);
        let computed = check_enum_shape_for(
            &binder,
            "Comp",
            0,
            vec![enum_member_named(
                "X",
                EnumMemberValue::Computed {
                    reason: "non-literal initializer is outside the subset".to_owned(),
                },
            )],
        );
        let mut ambient = check_enum_shape_for(
            &binder,
            "Amb",
            0,
            vec![enum_member_named("A", EnumMemberValue::Number(0.0))],
        );
        ambient.declared = true;
        let first = check_enum_shape_for(
            &binder,
            "Dup",
            0,
            vec![enum_member_named("X", EnumMemberValue::Number(0.0))],
        );
        let second = check_enum_shape_for(
            &binder,
            "Dup",
            0,
            vec![enum_member_named("Y", EnumMemberValue::Number(1.0))],
        );
        let input = EnumInput {
            enums: &[computed, ambient, first, second],
            interfaces: &[],
            namespaces: &[],
        };
        let decls = [
            enum_decl_for("a", 13, 23, "Comp", InitKind::Number, Some("0")),
            enum_decl_for("b", 24, 34, "Amb", InitKind::Number, Some("0")),
            enum_decl_for("c", 35, 45, "Dup", InitKind::Number, Some("0")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 3);
        assert!(
            report.unsupported[0].reason.contains("member 'X'"),
            "reason: {}",
            report.unsupported[0].reason
        );
        assert!(
            report.unsupported[1].reason.contains("ambient enum"),
            "reason: {}",
            report.unsupported[1].reason
        );
        assert!(
            report.unsupported[2]
                .reason
                .contains("multiple enum declarations"),
            "reason: {}",
            report.unsupported[2].reason
        );
    }

    #[test]
    fn enum_object_missing_and_non_literal_decline_or_diagnose() {
        let binder = binder_with(&[
            ("Color", span(0, 5)),
            ("o", span(6, 16)),
            ("m", span(17, 27)),
        ]);
        let shape = color_shape(&binder);
        let input = EnumInput {
            enums: &[shape],
            interfaces: &[],
            namespaces: &[],
        };
        let mut objected = enum_decl_for("o", 6, 16, "Color", InitKind::Number, None);
        objected.decl.init = None;
        objected.decl.init_object = Some(ObjectInit {
            members: Vec::new(),
            fresh: true,
        });
        let mut missing = enum_decl_for("m", 17, 27, "Color", InitKind::Number, None);
        missing.decl.init = None;
        let report = enums_report(&[objected, missing], &input, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '{}' is not assignable to type 'Color'."
        );
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("missing initializer"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn qualified_enums_resolve_with_short_names() {
        let binder = enum_binder(
            &[
                ("NS", 0, span(0, 2)),
                ("Dir", 1, span(10, 13)),
                ("w", 0, span(20, 30)),
                ("bad", 0, span(31, 44)),
                ("deep", 0, span(45, 60)),
            ],
            &[],
        );
        let dir = check_enum_shape_for(
            &binder,
            "Dir",
            1,
            vec![
                enum_member_named("Up", EnumMemberValue::Number(0.0)),
                enum_member_named("Down", EnumMemberValue::Number(1.0)),
            ],
        );
        let ns = namespace_shape_for(&binder, "NS", 0, 1, false, vec!["Dir"]);
        let input = EnumInput {
            enums: &[dir],
            interfaces: &[],
            namespaces: &[ns],
        };
        let decls = [
            enum_decl_for("w", 20, 30, "NS.Dir", InitKind::Number, Some("0")),
            enum_decl_for("bad", 31, 44, "NS.Dir", InitKind::Number, Some("9")),
            enum_decl_for("deep", 45, 60, "NS.Dir.Up", InitKind::Number, Some("5")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '9' is not assignable to type 'Dir'."
        );
        assert_eq!(
            report.diagnostics[1].message,
            "Type '5' is not assignable to type 'Dir.Up'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn qualified_misses_diagnose_ts2694_and_hidden_matches() {
        let binder = enum_binder(
            &[
                ("NS", 0, span(0, 2)),
                ("Hidden", 1, span(10, 16)),
                ("Hid", 1, span(17, 20)),
                ("a", 0, span(21, 35)),
                ("b", 0, span(36, 52)),
            ],
            &[],
        );
        let mut hidden = check_enum_shape_for(
            &binder,
            "Hidden",
            1,
            vec![enum_member_named("A", EnumMemberValue::Number(0.0))],
        );
        hidden.exported = false;
        let ns = namespace_shape_for(&binder, "NS", 0, 1, false, vec![]);
        let input = EnumInput {
            enums: &[hidden],
            interfaces: &[],
            namespaces: &[ns],
        };
        let decls = [
            enum_decl_for("a", 21, 35, "NS.Nope", InitKind::Number, Some("1")),
            enum_decl_for("b", 36, 52, "NS.Hidden", InitKind::Number, Some("0")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        for diagnostic in &report.diagnostics {
            assert_eq!(diagnostic.code, CODE_NO_EXPORTED_MEMBER);
        }
        assert_eq!(
            report.diagnostics[0].message,
            "Namespace 'NS' has no exported member 'Nope'."
        );
        assert_eq!(
            report.diagnostics[1].message,
            "Namespace 'NS' has no exported member 'Hidden'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn qualified_walk_up_hits_and_unclaimed_members_split() {
        // `NS.Nope` where a root `Nope` exists must NOT match the outer
        // declaration (scope-membership guard); `NS.VAL` (an exported value)
        // declines instead of mis-diagnosing (kind is unknowable).
        let binder = enum_binder(
            &[
                ("NS", 0, span(0, 2)),
                ("Nope", 0, span(3, 7)),
                ("VAL", 1, span(10, 13)),
                ("a", 0, span(21, 35)),
                ("b", 0, span(36, 50)),
            ],
            &[],
        );
        let ns = namespace_shape_for(&binder, "NS", 0, 1, false, vec!["VAL"]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[ns],
        };
        let decls = [
            enum_decl_for("a", 21, 35, "NS.Nope", InitKind::Number, Some("1")),
            enum_decl_for("b", 36, 50, "NS.VAL", InitKind::Number, Some("1")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_NO_EXPORTED_MEMBER);
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("not an enum or interface"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn qualified_unresolved_heads_skip_and_namespaces_as_types_diagnose() {
        let binder = enum_binder(
            &[
                ("NS", 0, span(0, 2)),
                ("a", 0, span(3, 17)),
                ("b", 0, span(18, 30)),
            ],
            &["NS2"],
        );
        let ns = namespace_shape_for(&binder, "NS", 0, 1, false, vec![]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[ns],
        };
        let decls = [
            enum_decl_for("a", 3, 17, "NS2.Foo", InitKind::Number, Some("1")),
            enum_decl_for("b", 18, 30, "NS", InitKind::Number, Some("1")),
        ];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_NAMESPACE_AS_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Cannot use namespace 'NS' as a type."
        );
        assert!(
            report.unsupported.is_empty(),
            "unresolved head skips silently"
        );
    }

    #[test]
    fn single_names_route_interfaces_namespaces_and_unknowns() {
        let binder = binder_with(&[
            ("Point", span(0, 5)),
            ("NS", span(6, 8)),
            ("v", span(9, 19)),
            ("w", span(20, 30)),
            ("u", span(31, 41)),
        ]);
        let mut point = interface_shape(&binder, "Point", 0, vec![("x", "number")]);
        point.exported = true;
        let ns = NamespaceShape {
            name: "NS".to_owned(),
            scope: 0,
            symbol: binder.resolve(FILE, 0, "NS"),
            span: span(0, 1),
            body_scope: u32::MAX,
            declared: false,
            exported: false,
            exported_members: Vec::new(),
        };
        let input = EnumInput {
            enums: &[],
            interfaces: &[point],
            namespaces: &[ns],
        };
        let good = EnumDecl {
            decl: object_decl("v", 9, 19, "Point", vec![("x", ObjectMemberKind::Number)]),
            init_text: None,
            cross_file_deps: Vec::new(),
        };
        let as_type = enum_decl_for("w", 20, 30, "NS", InitKind::Number, Some("1"));
        let unknown = enum_decl_for("u", 31, 41, "Nope", InitKind::Number, Some("1"));
        let report = enums_report(&[good, as_type, unknown], &input, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_NAMESPACE_AS_TYPE);
        assert_eq!(report.diagnostics[1].code, CODE_UNKNOWN_ANNOTATION);
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn qualified_trailing_namespace_mirrors_ts2749() {
        // Positional rule (probed tsc 7.0.2): single names get `TS2709`,
        // trailing qualified namespaces get `TS2749` on the full path.
        let binder = enum_binder(
            &[
                ("Outer", 0, span(0, 5)),
                ("Inner", 1, span(10, 15)),
                ("m", 0, span(20, 30)),
            ],
            &[],
        );
        let inner = namespace_shape_for(&binder, "Inner", 1, 2, true, vec![]);
        let outer = namespace_shape_for(&binder, "Outer", 0, 1, false, vec!["Inner"]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[outer, inner],
        };
        let decls = [enum_decl_for(
            "m",
            20,
            30,
            "Outer.Inner",
            InitKind::Number,
            Some("1"),
        )];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_VALUE_AS_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "'Outer.Inner' refers to a value, but is being used as a type here. Did you mean 'typeof Outer.Inner'?"
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn qualified_past_interface_mirrors_ts2713() {
        let binder = enum_binder(
            &[
                ("NS", 0, span(0, 2)),
                ("Point", 1, span(10, 15)),
                ("q", 0, span(20, 30)),
            ],
            &[],
        );
        let mut point = interface_shape(&binder, "Point", 1, vec![("x", "number")]);
        point.exported = true;
        let ns = namespace_shape_for(&binder, "NS", 0, 1, false, vec!["Point"]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[point],
            namespaces: &[ns],
        };
        let decls = [enum_decl_for(
            "q",
            20,
            30,
            "NS.Point.X",
            InitKind::Number,
            Some("1"),
        )];
        let report = enums_report(&decls, &input, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_TYPE_NOT_NAMESPACE);
        assert_eq!(
            report.diagnostics[0].message,
            "Cannot access 'Point.X' because 'Point' is a type, but not a namespace. Did you mean to retrieve the type of the property 'X' in 'Point' with 'Point[\"X\"]'?"
        );
        assert!(report.unsupported.is_empty());
    }

    /// One local alias shape for the P038 tests.
    fn alias_shape(name: &str, target: &str) -> TypeAliasShape {
        TypeAliasShape {
            name: name.to_owned(),
            target: target.to_owned(),
            has_type_params: false,
        }
    }

    /// One generic local alias shape (`type Box<T> = …`).
    fn generic_alias_shape(name: &str, target: &str) -> TypeAliasShape {
        TypeAliasShape {
            name: name.to_owned(),
            target: target.to_owned(),
            has_type_params: true,
        }
    }

    /// Runs [`check_file_with_aliases`] with local aliases (P038).
    fn file_report_with_aliases(
        decls: &[ConstDecl],
        aliases: &[TypeAliasShape],
        binder: &Binder,
    ) -> FileReport {
        let mut db = QueryDb::new();
        check_file_with_aliases(FILE, decls, binder, &mut db, aliases)
    }

    /// Runs [`check_enums_with_aliases`] with local aliases (P038).
    fn enums_report_with_aliases(
        decls: &[EnumDecl],
        input: &EnumInput<'_>,
        aliases: &[TypeAliasShape],
        binder: &Binder,
    ) -> FileReport {
        let mut db = QueryDb::new();
        check_enums_with_aliases(FILE, decls, input, aliases, binder, &mut db)
    }

    #[test]
    fn local_alias_primitive_rewrites_spelling() {
        // Probed tsc 7.0.2 (p038-probes/b-wrong.ts): `Num` checks exactly
        // like `number`, clean or `TS2322`.
        let binder = binder_with(&[
            ("Num", span(0, 3)),
            ("ok", span(10, 20)),
            ("bad", span(30, 40)),
        ]);
        let aliases = [alias_shape("Num", "number")];
        let decls = [
            decl("ok", 10, 20, "Num", InitKind::Number),
            decl("bad", 30, 40, "Num", InitKind::String),
        ];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_boundary_rewrites_spelling() {
        // Probed tsc 7.0.2 (p038-probes/k-boundary.ts): `any`/`unknown`
        // admit bearing values while `never` rejects literals.
        let binder = binder_with(&[
            ("An", span(0, 2)),
            ("U2", span(3, 5)),
            ("Nev", span(6, 9)),
            ("a", span(10, 20)),
            ("u", span(21, 31)),
            ("n", span(32, 42)),
        ]);
        let aliases = [
            alias_shape("An", "any"),
            alias_shape("U2", "unknown"),
            alias_shape("Nev", "never"),
        ];
        let decls = [
            decl("a", 10, 20, "An", InitKind::Number),
            decl("u", 21, 31, "U2", InitKind::Number),
            decl("n", 32, 42, "Nev", InitKind::Number),
        ];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert!(
            report.diagnostics[0]
                .message
                .ends_with("is not assignable to type 'never'."),
            "message: {}",
            report.diagnostics[0].message
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_chained_declines() {
        // Probed tsc 7.0.2 (p038-probes/d-chain.ts): tsc resolves
        // transitively, so the single-level decline is a pinned divergence.
        let binder = binder_with(&[("A", span(0, 1)), ("B", span(2, 3)), ("b", span(4, 14))]);
        let aliases = [alias_shape("A", "number"), alias_shape("B", "A")];
        let decls = [decl("b", 4, 14, "B", InitKind::Number)];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("chained aliases"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn local_alias_generic_declines_bare_and_head() {
        // Probed tsc 7.0.2 (p038-probes/f-generic.ts): clean in tsc, so
        // both declines are pinned divergences — never a forced `PITH2304`.
        let binder = binder_with(&[
            ("Box", span(0, 3)),
            ("b", span(10, 20)),
            ("h", span(30, 40)),
        ]);
        let aliases = [generic_alias_shape("Box", "T")];
        let decls = [
            decl("b", 10, 20, "Box", InitKind::Number),
            decl("h", 30, 40, "Box<number>", InitKind::Number),
        ];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 2);
        for note in &report.unsupported {
            assert!(note.reason.contains("generic"), "reason: {}", note.reason);
        }
    }

    #[test]
    fn local_alias_circular_declines() {
        // Probed tsc 7.0.2 (p038-probes/g-circular.ts): tsc reports
        // `TS2456` at the declaration, which the subset never synthesizes.
        let binder = binder_with(&[("A", span(0, 1)), ("a", span(2, 12))]);
        let aliases = [alias_shape("A", "A")];
        let decls = [decl("a", 2, 12, "A", InitKind::Number)];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("circular"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn local_alias_complex_target_declines() {
        // Probed tsc 7.0.2 (p038-probes/h-complex.ts): union and object
        // targets check in tsc; the subset declines instead of spelling them.
        let binder = binder_with(&[
            ("U", span(0, 1)),
            ("S", span(2, 3)),
            ("u", span(10, 20)),
            ("s", span(30, 40)),
        ]);
        let aliases = [
            alias_shape("U", "number | string"),
            alias_shape("S", "{ x: number }"),
        ];
        let decls = [
            decl("u", 10, 20, "U", InitKind::Number),
            decl("s", 30, 40, "S", InitKind::Number),
        ];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 2);
        for note in &report.unsupported {
            assert!(
                note.reason.contains("non-identifier"),
                "reason: {}",
                note.reason
            );
        }
    }

    #[test]
    fn local_alias_shadowed_by_const_declines() {
        // Probed tsc 7.0.2 (p038-probes/e-shadow.ts): clean in tsc, which
        // reads the type meaning past the value. The solver declines so an
        // expansion can never hijack a value binding (pinned divergence).
        let binder = binder_with(&[("Alias", span(0, 5)), ("n", span(10, 20))]);
        let aliases = [alias_shape("Alias", "number")];
        let decls = [
            decl("Alias", 0, 5, "string", InitKind::String),
            decl("n", 10, 20, "Alias", InitKind::Number),
        ];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("shadows"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn local_alias_multiple_declines() {
        // Duplicate aliases are `TS2300` in tsc; the subset records the gap.
        let binder = binder_with(&[("Dup", span(0, 3)), ("d", span(10, 20))]);
        let aliases = [alias_shape("Dup", "number"), alias_shape("Dup", "string")];
        let decls = [decl("d", 10, 20, "Dup", InitKind::Number)];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("multiple type alias"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn local_alias_shape_target_declines_in_check_file() {
        // `check_file_with_aliases` holds no shape tables, so named-shape
        // targets decline with the entry-point reason;
        // [`check_enums_with_aliases`] relinks them.
        let binder = binder_with(&[("Alias", span(0, 5)), ("a", span(10, 20))]);
        let aliases = [alias_shape("Alias", "Point")];
        let decls = [decl("a", 10, 20, "Alias", InitKind::Number)];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0]
                .reason
                .contains("interface/enum paths"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn local_alias_unknown_name_still_2304() {
        // Names no alias claims keep the historical `PITH2304`.
        let binder = binder_with(&[("x", span(0, 10))]);
        let aliases = [alias_shape("Num", "number")];
        let decls = [decl("x", 0, 10, "Nope", InitKind::Number)];
        let report = file_report_with_aliases(&decls, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_interface_relinks_with_underlying_spelling() {
        // Probed tsc 7.0.2 (p038-probes/b-wrong.ts, c-missing.ts): wrong
        // members diagnose per member, missing members spell the UNDERLYING
        // interface (alias transparency).
        let binder = binder_with(&[
            ("Point", span(0, 5)),
            ("Alias", span(6, 11)),
            ("good", span(20, 30)),
            ("wrong", span(40, 50)),
            ("missing", span(60, 70)),
        ]);
        let point = interface_shape(&binder, "Point", 0, vec![("x", "number"), ("y", "number")]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[point],
            namespaces: &[],
        };
        let aliases = [alias_shape("Alias", "Point")];
        let decls = [
            EnumDecl {
                decl: object_decl(
                    "good",
                    20,
                    30,
                    "Alias",
                    vec![
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                ),
                init_text: None,
                cross_file_deps: Vec::new(),
            },
            EnumDecl {
                decl: object_decl(
                    "wrong",
                    40,
                    50,
                    "Alias",
                    vec![
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::String),
                    ],
                ),
                init_text: None,
                cross_file_deps: Vec::new(),
            },
            EnumDecl {
                decl: object_decl(
                    "missing",
                    60,
                    70,
                    "Alias",
                    vec![("x", ObjectMemberKind::Number)],
                ),
                init_text: None,
                cross_file_deps: Vec::new(),
            },
        ];
        let report = enums_report_with_aliases(&decls, &input, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 2);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert_eq!(report.diagnostics[1].code, CODE_MISSING_MEMBER);
        assert_eq!(
            report.diagnostics[1].message,
            "Property 'y' is missing in type '{ x: number; }' but required in type 'Point'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_enum_relinks_with_underlying_spelling() {
        // Probed tsc 7.0.2 (p038-probes/i-enum.ts): values spell the
        // underlying enum (`type 'Color'`).
        let binder = binder_with(&[
            ("Color", span(0, 5)),
            ("C", span(6, 7)),
            ("a", span(10, 20)),
            ("b", span(30, 40)),
        ]);
        let shape = color_shape(&binder);
        let input = EnumInput {
            enums: &[shape],
            interfaces: &[],
            namespaces: &[],
        };
        let aliases = [alias_shape("C", "Color")];
        let decls = [
            enum_decl_for("a", 10, 20, "C", InitKind::Number, Some("1")),
            enum_decl_for("b", 30, 40, "C", InitKind::Number, Some("5")),
        ];
        let report = enums_report_with_aliases(&decls, &input, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type '5' is not assignable to type 'Color'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_primitive_rewrites_through_enums() {
        // The enums entry rewrites primitives exactly like [`check_file`].
        let binder = binder_with(&[("Num", span(0, 3)), ("b", span(10, 20))]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[],
        };
        let aliases = [alias_shape("Num", "number")];
        let decls = [enum_decl_for(
            "b",
            10,
            20,
            "Num",
            InitKind::String,
            Some("\"oops\""),
        )];
        let report = enums_report_with_aliases(&decls, &input, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'string' is not assignable to type 'number'."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_unclaimed_target_declines_through_enums() {
        // Targets no shape owns decline instead of verdicting.
        let binder = binder_with(&[("Z", span(0, 1)), ("z", span(10, 20))]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[],
        };
        let aliases = [alias_shape("Z", "Nowhere")];
        let decls = [enum_decl_for("z", 10, 20, "Z", InitKind::Number, Some("1"))];
        let report = enums_report_with_aliases(&decls, &input, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("no interface, enum"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }

    #[test]
    fn local_alias_namespace_target_diagnoses_2709() {
        // Probed tsc 7.0.2 (p038-probes/l-ns-target.ts): tsc reports
        // `TS2709` at the alias declaration; the solver mirrors the family
        // at the use (disclosed anchor divergence).
        let binder = enum_binder(
            &[
                ("NS", 0, span(0, 2)),
                ("N", 0, span(3, 4)),
                ("v", 0, span(10, 20)),
            ],
            &[],
        );
        let ns = namespace_shape_for(&binder, "NS", 0, 1, false, vec![]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[ns],
        };
        let aliases = [alias_shape("N", "NS")];
        let decls = [enum_decl_for("v", 10, 20, "N", InitKind::Number, Some("1"))];
        let report = enums_report_with_aliases(&decls, &input, &aliases, &binder);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_NAMESPACE_AS_TYPE);
        assert_eq!(
            report.diagnostics[0].message,
            "Cannot use namespace 'NS' as a type."
        );
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn local_alias_shadowed_declines_through_enums() {
        // The const-shadowing guard holds on the enums entry too.
        let binder = binder_with(&[("Alias", span(0, 5)), ("n", span(10, 20))]);
        let input = EnumInput {
            enums: &[],
            interfaces: &[],
            namespaces: &[],
        };
        let aliases = [alias_shape("Alias", "number")];
        let decls = [
            enum_decl_for("Alias", 0, 5, "string", InitKind::String, Some("\"hello\"")),
            enum_decl_for("n", 10, 20, "Alias", InitKind::Number, Some("1")),
        ];
        let report = enums_report_with_aliases(&decls, &input, &aliases, &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("shadows"),
            "reason: {}",
            report.unsupported[0].reason
        );
    }
}
