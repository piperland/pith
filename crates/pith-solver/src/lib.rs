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
//! - `let` checks exactly like `const` (mutability/reassignment unchecked).
//!
//! Out-of-subset declarations (union annotations outside [`check_narrowing`],
//! missing annotations, non-literal or missing initializers, union/complex
//! member types, empty `{}` annotations, stale-literal excess candidates,
//! contradictory primitive/object initializer pairs) are recorded as
//! [`UnsupportedDecl`] entries, never silently dropped.
//!
//! BLOCKER (P004 adapter gap): [`ConstDecl::annotation`], [`ConstDecl::init`],
//! and [`ConstDecl::init_object`] are stand-ins for the missing adapter facts
//! `DeclAnnotationFact` (annotation text + span), `InitLiteralFact`
//! (initializer literal kind + span), and `ObjectMemberFact`s (member name +
//! literal kind per `{ ... }` entry). `ParsedFile` v1 carries declaration
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
//! (straight-line single `return` only), then delegates checkable returns
//! through synthetic [`ConstDecl`]s to the same primitive/object paths, so
//! `TS2322`/`TS2304`/object-family verdicts match by construction.
//! Occurrence nodes for synthetic returns live in a disjoint range (see
//! `function_occurrence_node`), so consts and functions for one file may
//! share a [`QueryDb`]. Params, return annotations, and body shapes are
//! fact-fed from the adapter's function declarator facts; only the
//! literal-kind enum mapping is driver-side (mechanical and exhaustive).
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
//! - Range/variadic arities are declined: optional/defaulted params spell
//!   `Expected 1-2 arguments, but got 3.` and rest params spell `TS2555`
//!   (`Expected at least 1 arguments, but got 0.`); the subset checks exact
//!   counts only. Overload failures spell `TS2769` with continuation lines;
//!   multiple same-name declarations (overloads, or shadowing the fact set
//!   cannot disambiguate — a documented precision limit) decline with reason.
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
//!   construct signatures, and optional members decline with per-member
//!   reasons (pinned oracle-clean divergences: tsc checks all of these).
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
/// Code for call-site argument-type mismatches (oracle `TS2345`).
pub const CODE_ARG_TYPE: &str = "PITH2345";
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
            Self::NonLiteral => TypeStore::UNKNOWN,
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
            Self::NonLiteral => "unknown",
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
}

/// One function parameter: name + whether it carries a type annotation.
///
/// Fact-fed from the adapter's identifier parameter list. The return checker
/// gates on `annotated` only; the call-site checker additionally needs
/// `annotation` (arg-type checks), `optional`, and `is_rest` (exact-arity
/// checks decline range/variadic lists).
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
/// the return is an object literal), `init_object` the member facts (always
/// fresh — only direct syntactic literals carry them). A
/// `Some(NonLiteral)` kind declines before delegation; the impossible pairs
/// (`Some` + `Some`, `None` + `None`) delegate into the shared
/// contradictory/missing unsupported paths rather than growing
/// function-specific ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionReturn {
    /// Literal kind; `None` iff the return is an object literal.
    pub kind: Option<InitKind>,
    /// Object-literal members when the return is `{ ... }`; `None` otherwise.
    pub init_object: Option<ObjectInit>,
}

/// Body shapes of one function declaration.
///
/// Only [`FunctionBody::SingleReturn`] is checkable; the rest decline to
/// [`UnsupportedDecl`] with distinct reasons.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionBody {
    /// Exactly one statement, `return <expr>;` with an argument.
    SingleReturn(FunctionReturn),
    /// No body node: `declared` tells `declare function` apart from an
    /// overload signature.
    NoBody {
        /// `true` for `declare function` (ambient, never has a body).
        declared: bool,
    },
    /// A body with no statements.
    Empty,
    /// Anything else: multiple returns, branches, loops, bare or missing
    /// `return`.
    Complex,
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
    /// Raw return annotation text; `None` means unannotated.
    pub return_annotation: Option<String>,
    /// Body shape; only [`FunctionBody::SingleReturn`] is checkable.
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
        check_one(
            file,
            occurrence_node(index),
            decl,
            binder,
            db,
            &freshness,
            &mut report,
        );
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
/// annotated, return annotated, single literal `return`) delegate to the
/// same [`check_one`] path as [`check_file`] through a synthetic
/// [`ConstDecl`] — the return literal as initializer, always fresh — so
/// verdicts and messages match the const/object subset by construction.
///
/// Occurrence identity lives in a disjoint node range (see
/// `function_occurrence_node`): consts and functions for one file may share
/// a [`QueryDb`] without aliasing memo entries.
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
            Ok((annotation, kind, init_object)) => synth.push(ConstDecl {
                name: decl.name.clone(),
                span: decl.span,
                scope: decl.scope,
                symbol: decl.symbol,
                kind: DeclKind::Function,
                annotation: Some(annotation.to_owned()),
                init: kind,
                init_object,
            }),
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
        check_one(
            file,
            function_occurrence_node(index),
            decl,
            binder,
            db,
            &freshness,
            &mut report,
        );
    }
    sort_report(&mut report);
    report
}

/// Gates one function declaration: `Ok` carries the return annotation text,
/// return literal kind, and object members for the synthetic [`ConstDecl`];
/// `Err` carries the unsupported reason.
fn function_shape(
    decl: &FunctionDecl,
) -> Result<(&str, Option<InitKind>, Option<ObjectInit>), String> {
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
    let body = match &decl.body {
        FunctionBody::SingleReturn(body) => body,
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
        FunctionBody::Complex => {
            return Err(format!(
                "complex body on '{}': control flow is outside the subset",
                decl.name
            ));
        }
    };
    if body.kind == Some(InitKind::NonLiteral) {
        return Err(format!(
            "non-literal return in '{}' is outside the subset",
            decl.name
        ));
    }
    Ok((annotation, body.kind, body.init_object.clone()))
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
/// - Several declarations bear the name (overloads, or shadowing the
///   fact set cannot disambiguate): one [`UnsupportedDecl`] — overload
///   resolution is future work, never speculative.
/// - Exactly one declaration: parameter gates (structural first —
///   `params_complex`, unannotated, optional/rest, uncheckable parameter
///   types — each its own [`UnsupportedDecl`] at the callee span), then at
///   most one diagnostic: arity (`PITH2554`) beats arg types (`PITH2345`),
///   and only the first mismatched argument reports (both probed on tsc
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
        report.unsupported.push(UnsupportedDecl {
            file,
            span: call.callee_span,
            reason: format!(
                "multiple declarations for '{}': overload resolution is outside the subset",
                call.callee
            ),
        });
        return;
    }
    let decl = &decls[candidates[0]];
    let Some(params) = call_params(call, decl, file, report) else {
        return;
    };
    if call.args.len() != params.len() {
        let span = if call.args.len() < params.len() {
            call.callee_span
        } else {
            call.args[params.len()].span
        };
        report.diagnostics.push(PithDiagnostic {
            code: CODE_ARITY.to_owned(),
            file,
            span,
            message: format!(
                "Expected {} arguments, but got {}.",
                params.len(),
                call.args.len()
            ),
        });
        return;
    }
    for (argument, (expected, display)) in call.args.iter().zip(params.iter()) {
        if argument.kind == InitKind::NonLiteral {
            continue;
        }
        if argument.kind.type_id() != *expected {
            report.diagnostics.push(PithDiagnostic {
                code: CODE_ARG_TYPE.to_owned(),
                file,
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

/// Gates one call's parameter list for [`check_one_call`].
///
/// `Some` carries per-parameter `(expected [``TypeId``], display text)` in
/// source order; `None` means one [`UnsupportedDecl`] was pushed at the
/// callee span and the call declines. Structural gates run
/// parameter-by-parameter in order (unannotated, optional/rest, then
/// uncheckable type text): the first failure wins, so reasons stay
/// single and deterministic.
fn call_params(
    call: &CallSite,
    decl: &FunctionDecl,
    file: FileId,
    report: &mut FileReport,
) -> Option<Vec<(TypeId, String)>> {
    if decl.params_complex {
        decline(
            call,
            file,
            report,
            "non-identifier parameter pattern is outside the subset",
        );
        return None;
    }
    let mut params = Vec::with_capacity(decl.params.len());
    for param in &decl.params {
        if !param.annotated {
            decline(
                call,
                file,
                report,
                &format!(
                    "unannotated parameter '{}' is outside the subset",
                    param.name
                ),
            );
            return None;
        }
        if param.optional {
            decline(
                call,
                file,
                report,
                &format!(
                    "optional parameter '{}' takes a range of arities, outside the subset",
                    param.name
                ),
            );
            return None;
        }
        if param.is_rest {
            decline(
                call,
                file,
                report,
                &format!(
                    "rest parameter '{}' is variadic, outside the subset",
                    param.name
                ),
            );
            return None;
        }
        match classify_param(param) {
            Ok((expected, display)) => params.push((expected, display)),
            Err(reason) => {
                decline(call, file, report, &reason);
                return None;
            }
        }
    }
    Some(params)
}

/// Pushes one call-site [`UnsupportedDecl`] at the callee span.
fn decline(call: &CallSite, file: FileId, report: &mut FileReport, reason: &str) {
    report.unsupported.push(UnsupportedDecl {
        file,
        span: call.callee_span,
        reason: format!("call to '{}': {reason}", call.callee),
    });
}

/// Classifies one annotated, non-optional, non-rest parameter into its
/// expected ([`TypeId`], display text): `Err` carries the decline reason
/// (union, object, unknown, or missing type text the subset cannot spell
/// argument checks against).
fn classify_param(param: &FunctionParam) -> Result<(TypeId, String), String> {
    let text = param.annotation.as_deref().map_or("", str::trim);
    if text.contains('|') {
        return Err(format!(
            "union parameter type '{text}' is outside the subset"
        ));
    }
    annotation_type(text).map_or_else(
        || {
            Err(format!(
                "parameter type '{text}' for '{}' is outside the subset",
                param.name
            ))
        },
        |expected| Ok((expected, text.to_owned())),
    )
}

/// Generic functions (P016, probed on tsc 7.0.2 `--strict --pretty false`).
///
/// [`check_generics`] checks identity-style `function id<T>(x: T): T`
/// declarations with explicit type arguments AND single-candidate inference
/// from argument literals. The (inferred or explicit) type argument binds in
/// the scoped [`InferenceTable`], substitutes for `T` in the parameter
/// annotation text, and checks through the same primitive comparisons (and
/// message shapes) as [`check_calls`]. Bodies check against `T` directly at
/// declaration level, exactly like tsc (call-independent).
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
/// - Declines, all probed: multi-parameter `pair<T, U>` (clean call),
///   constrained `idc("s")` (clean), defaulted `idd(1)` (clean) — solver
///   declines each (pinned oracle-clean divergences). Union parameter
///   `x: T | string` and object return `: { v: T }` error in tsc ITSELF
///   (the `return x` fails: `Type 'string | T' is not assignable to type
///   'T'.`, `Type 'T' is not assignable to type '{ v: T; }'.`) — solver
///   declines with reasons (pinned oracle-error divergences).
/// - Multi-parameter inference `f(1, "s")` over `(x: T, y: T)` binds the
///   literal type `1`, then `TS2345` on `"s"`: literal-type inference is
///   outside the subset (multi-parameter lists decline before any call
///   checks).
///
/// Corollaries a generic declaration is never decl-silent: literal bodies
/// always diagnose (no literal inhabits bare `T`), non-literal bodies
/// decline, and every other shape declines. Calls verify independently.
///
/// Design law (H-002): inferred bindings are per-occurrence side state in
/// [`InferenceTable`], keyed by `(file, node)` — never in
/// [`TypeData`](pith_types::TypeData). Instantiation resolves to shared
/// builtin [`TypeId`]s through [`annotation_type`] (the shared interner's
/// canonical ids), so no parallel universe is interned and nothing here
/// needs the [`QueryDb`] memo (there is no new structure to memoize).
///
/// Code for explicit type-argument count mismatches (oracle `TS2558`).
pub const CODE_TYPE_ARITY: &str = "PITH2558";

/// One generic `function id<T>(x: T): T` declaration: the plain
/// [`FunctionDecl`] plus its declared type-parameter names verbatim from
/// adapter facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GenericDecl {
    /// The underlying declaration (name/span/scope/symbol/params/return/body).
    pub decl: FunctionDecl,
    /// Declared type-parameter names in source order (`["T"]` for `id<T>`).
    pub type_params: Vec<String>,
    /// `true` when any parameter carries a constraint, a default, or an
    /// `in`/`out`/`const` modifier (from the adapter's complexity flag).
    pub type_params_complex: bool,
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
/// Maps each generic call occurrence to the [`TypeId`] its type parameter
/// bound — inferred from the single literal argument, or resolved from the
/// explicit type argument. Instantiated structure is shared and canonical
/// (builtins through [`annotation_type`]); THIS table holds only the
/// occurrence-varying binding, keyed by `(file, node)`.
#[derive(Clone, Debug, Default)]
struct InferenceTable {
    bindings: HashMap<(FileId, NodeId), TypeId>,
}

impl InferenceTable {
    /// The recorded binding for one call occurrence, if any.
    #[must_use]
    fn binding(&self, file: FileId, node: NodeId) -> Option<TypeId> {
        self.bindings.get(&(file, node)).copied()
    }
}

/// What a checkable generic declaration carries into call checking: the
/// single bound type-parameter name (body verdicts emit at declaration
/// level, so calls only need the name for decline-free gating).
#[derive(Clone, Debug, PartialEq, Eq)]
struct GenericShape {
    /// The single bound type-parameter name (`T`).
    t_name: String,
}

/// Checks every generic declaration in `decls` plus every instantiation in
/// `calls` for `file`, returning the sorted [`FileReport`].
///
/// Declaration phase (one note max per declaration, structural first):
/// type-parameter gates (complex, count), parameter gates (patterns,
/// annotatedness, optionality, exactly one bare-`T` annotation), return
/// gates (present, bare `T`), then the body check (literal returns diagnose
/// against `T` directly; non-literal returns and every other shape decline).
/// A generic declaration is never decl-silent (see the module docs).
///
/// Call phase (one diagnostic max per call): name resolution mirrors
/// [`check_calls`] (unresolved callees skip, overloads decline); calls to
/// declined declarations skip silently (the declaration note covers them).
/// Then arity (`PITH2554`, exact single argument), `T` resolution (explicit
/// count `PITH2558` / unknown `PITH2304` / complex-type-argument decline, or
/// single-literal inference with a no-candidate decline), and finally the
/// substituted argument check (`PITH2345`, vacuous for inferred calls by
/// construction). Non-literal arguments under explicit type arguments skip
/// per-argument (P014 precedent); under inference they decline (no
/// candidate).
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
    }
    Some(shape)
}

/// Gates one generic declaration's type parameters, value parameters, and
/// return annotation into a [`GenericShape`]; `Err` carries the reason.
///
/// Gate order is structural-first: type-parameter complexity and count,
/// then value-parameter patterns/annotatedness/optionality/count, then
/// bare-`T` annotation shapes, then the return annotation. The body checks
/// separately in [`check_generic_body`].
fn generic_decl_shape(generic: &GenericDecl) -> Result<GenericShape, String> {
    if generic.type_params_complex {
        return Err(
            "type parameter constraint, default, or modifier is outside the subset".to_owned(),
        );
    }
    if generic.type_params.len() != 1 {
        if generic.type_params.is_empty() {
            return Err(format!(
                "no type parameters on '{}': not a generic declaration",
                generic.decl.name
            ));
        }
        return Err(format!(
            "multiple type parameters '{}' are outside the subset",
            generic.type_params.join(", ")
        ));
    }
    let t_name = generic.type_params[0].clone();
    let decl = &generic.decl;
    if decl.params_complex {
        return Err("non-identifier parameter pattern is outside the subset".to_owned());
    }
    if decl.params.len() != 1 {
        return Err(format!(
            "generic function '{}' has {} parameters: exactly one is in the subset",
            decl.name,
            decl.params.len()
        ));
    }
    let param = &decl.params[0];
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
    bare_t_param(
        param.annotation.as_deref().map_or("", str::trim),
        &t_name,
        param.name.as_str(),
    )?;
    let annotation = decl.return_annotation.as_deref().map_or("", str::trim);
    if decl.return_annotation.is_none() {
        return Err(format!(
            "no return annotation on '{}': inference is outside the subset",
            decl.name
        ));
    }
    bare_t_return(annotation, &t_name)?;
    Ok(GenericShape { t_name })
}

/// Requires a value-parameter annotation to be exactly the bare type
/// parameter (`T`); union/object/other shapes decline with distinct reasons.
fn bare_t_param(text: &str, t_name: &str, param: &str) -> Result<(), String> {
    if text == t_name {
        return Ok(());
    }
    if text.contains('|') {
        return Err(format!(
            "union parameter type '{text}' is outside the subset"
        ));
    }
    if text.starts_with('{') {
        return Err(format!(
            "object parameter type '{text}' is outside the subset"
        ));
    }
    Err(format!(
        "parameter type '{text}' for '{param}' is not the bare type parameter '{t_name}': outside the subset"
    ))
}

/// Requires the return annotation to be exactly the bare type parameter
/// (`T`); union/object/other shapes decline with distinct reasons.
fn bare_t_return(text: &str, t_name: &str) -> Result<(), String> {
    if text == t_name {
        return Ok(());
    }
    if text.contains('|') {
        return Err(format!("union return type '{text}' is outside the subset"));
    }
    if text.starts_with('{') {
        return Err(format!("object return type '{text}' is outside the subset"));
    }
    Err(format!(
        "return type '{text}' is not the bare type parameter '{t_name}': outside the subset"
    ))
}

/// Emits one generic declaration's body verdict, returning its
/// [`GenericShape`] for call checking.
///
/// Literal bodies always diagnose against `T` (no literal inhabits bare
/// `T` — probed tsc 7.0.2); non-literal returns decline (the `T`-typed
/// pass-through is clean in tsc but inexpressible without expression
/// facts). Returns `Some` in both cases: calls check independently of body
/// checkability (P014 precedent).
#[must_use]
fn check_generic_body(
    file: FileId,
    span: Span,
    name: &str,
    shape: &GenericShape,
    body: &FunctionReturn,
    report: &mut FileReport,
) -> Option<GenericShape> {
    let t_name = shape.t_name.as_str();
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

/// Checks one generic instantiation, pushing into the context report.
///
/// At most one diagnostic ever fires per call (arity before resolution
/// before argument types); declines push exactly one [`UnsupportedDecl`].
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
    if call.args.len() != 1 {
        let span = if call.args.is_empty() {
            call.callee_span
        } else {
            call.args[1].span
        };
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_ARITY.to_owned(),
            file,
            span,
            message: format!("Expected 1 arguments, but got {}.", call.args.len()),
        });
        return;
    }
    let Some((bound, display)) = resolve_t(node, &shape, call_site, ctx) else {
        return;
    };
    let argument = &call.args[0];
    if argument.kind == InitKind::NonLiteral {
        // Reachable only under explicit type arguments (inference declines
        // non-literals during resolution): skip per-argument, P014 precedent.
        return;
    }
    if argument.kind.type_id() != bound {
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_ARG_TYPE.to_owned(),
            file,
            span: argument.span,
            message: format!(
                "Argument of type '{}' is not assignable to parameter of type '{display}'.",
                argument.kind.name(),
            ),
        });
    }
}

/// Resolves `T` for one call to its builtin [`TypeId`] plus display text,
/// recording the binding in the [`InferenceTable`].
///
/// Explicit arguments gate count (`PITH2558`), then name
/// (`PITH2304` for unknown names, decline for union/object shapes tsc
/// accepts but the subset cannot spell checks against). Inference binds
/// the single literal argument's kind and declines non-literals (no
/// candidate without expression facts). Returns `None` when one note was
/// pushed and the call declines.
#[must_use]
fn resolve_t(
    node: NodeId,
    shape: &GenericShape,
    call_site: &GenericCall,
    ctx: &mut GenericCallCtx<'_, '_>,
) -> Option<(TypeId, String)> {
    let call = &call_site.call;
    let file = ctx.file;
    if let Some(texts) = call_site.explicit_args.as_ref() {
        if texts.len() != 1 {
            ctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_TYPE_ARITY.to_owned(),
                file,
                span: call.callee_span,
                message: format!("Expected 1 type arguments, but got {}.", texts.len()),
            });
            return None;
        }
        let text = texts[0].trim();
        if text.contains('|') || text.starts_with('{') {
            ctx.report.unsupported.push(UnsupportedDecl {
                file,
                span: call.callee_span,
                reason: format!(
                    "call to '{}': type argument '{text}' is outside the subset",
                    call.callee
                ),
            });
            return None;
        }
        let Some(bound) = annotation_type(text) else {
            ctx.report.diagnostics.push(PithDiagnostic {
                code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                file,
                span: call.callee_span,
                message: format!("Cannot find name '{text}'."),
            });
            return None;
        };
        ctx.inference.bindings.insert((file, node), bound);
        // Verdicts below substitute the RECORDED binding, never the
        // transient local: occurrence-varying state flows through the
        // scoped side table (H-002), even though the two agree here.
        let bound = ctx.inference.binding(file, node).unwrap_or(bound);
        return Some((bound, text.to_owned()));
    }
    let argument = &call.args[0];
    if argument.kind == InitKind::NonLiteral {
        ctx.report.unsupported.push(UnsupportedDecl {
            file,
            span: argument.span,
            reason: format!(
                "call to '{}': cannot infer '{}' from a non-literal argument: expression facts are outside the subset",
                call.callee, shape.t_name
            ),
        });
        return None;
    }
    let bound = argument.kind.type_id();
    let display = primitive_name(bound).unwrap_or("unknown").to_owned();
    ctx.inference.bindings.insert((file, node), bound);
    // Same read-back as the explicit path: substitute the recorded
    // binding (H-002), never the transient local.
    let bound = ctx.inference.binding(file, node).unwrap_or(bound);
    Some((bound, display))
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
/// over primitives) plus identifier-initializer *uses* of those consts
/// (`const b: string = x;`) against [`TypeofGuard`] regions. Non-union
/// declarations delegate to [`check_one`] unchanged, so verdicts outside
/// narrowing match by construction.
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

/// Whether `inner` lies fully inside `outer` (same file, closed bounds).
fn span_contains(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.lo <= inner.lo && inner.hi <= outer.hi
}

/// Checks union-annotated declarations plus identifier-uses for `file`,
/// returning the sorted [`FileReport`].
///
/// Declaration routing: object annotations delegate to [`check_one`];
/// unions parse to canonical members (unknown names diagnose `PITH2304` like
/// object members, shapes/degenerates decline); only missing-init and
/// non-literal-init targets enter the narrowing environment (literal-init
/// targets check against the union but never narrow — probed tsc 7.0.2).
/// Non-union declarations delegate to [`check_one`] unchanged.
///
/// Use routing, in order: expected-type gating (single primitives check;
/// object/union/unknown spellings repeat [`check_one`]'s verdicts), target
/// linkage (unknown targets keep the legacy non-literal note; shadowed or
/// closure-ambiguous targets decline), literal-init targets decline, decline
/// regions decline, then guard refinement (all applicable guards must agree
/// on one primitive; complements that are not single primitives decline;
/// guard literals outside the union decline positive branches and fall back
/// to the full union on complements). Unguarded uses diagnose over the full
/// union spelling.
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
    let mut env: Vec<UnionTarget> = Vec::new();
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
    if annotation.starts_with('{') {
        let mut ctx = CheckCtx {
            file,
            node,
            db,
            freshness,
            report,
        };
        check_object(decl, span, annotation, &mut ctx);
        return;
    }
    if !annotation.contains('|') {
        check_one(file, node, decl, binder, db, freshness, report);
        return;
    }
    let pieces: Vec<&str> = annotation.split('|').map(str::trim).collect();
    let mut unknown: Vec<&str> = Vec::new();
    let mut shaped = false;
    for piece in pieces {
        if annotation_type(piece).is_none() {
            if piece
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
                && !piece.is_empty()
            {
                unknown.push(piece);
            } else {
                shaped = true;
            }
        }
    }
    if !unknown.is_empty() {
        for name in unknown {
            report.diagnostics.push(PithDiagnostic {
                code: CODE_UNKNOWN_ANNOTATION.to_owned(),
                file,
                span,
                message: format!("Cannot find name '{name}'."),
            });
        }
        return;
    }
    if shaped {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("union member shape in '{annotation}' is outside the subset"),
        });
        return;
    }
    let Some(members) = parse_union_annotation(annotation) else {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("degenerate union annotation '{annotation}' is outside the subset"),
        });
        return;
    };
    let spelling = union_spelling(&members);
    if decl.init_object.is_some() {
        report.unsupported.push(UnsupportedDecl {
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
            nctx.env.push(UnionTarget {
                name: decl.name.clone(),
                members,
                spelling,
                has_literal_init: false,
            });
        }
        Some(InitKind::NonLiteral) => {
            nctx.report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: "non-literal initializer is outside the subset".to_owned(),
            });
            nctx.env.push(UnionTarget {
                name: decl.name.clone(),
                members,
                spelling,
                has_literal_init: false,
            });
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

/// Fact slices feeding [`check_narrowing`], bundled so the entry point
/// stays lean: identifier uses, `typeof` guards, and decline regions.
#[derive(Debug)]
pub struct NarrowingFacts<'a> {
    /// Identifier uses of union-annotated consts.
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
    env: &'a mut Vec<UnionTarget>,
    report: &'a mut FileReport,
}

/// Read-only checking state for one [`check_narrowing`] identifier-use.
struct NarrowUseCtx<'a> {
    guards: &'a [TypeofGuard],
    declines: &'a [DeclineRegion],
    env: &'a [UnionTarget],
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
    target: &'a UnionTarget,
}

/// Links one identifier-use to its narrowing target: span resolution,
/// expected-type gating, target linkage, ambiguity and literal-init checks.
///
/// Returns `None` when the use declines (one [`UnsupportedDecl`] pushed).
/// Guard refinement runs separately in [`refine_use`].
fn link_use_target<'a>(
    file: FileId,
    use_: &NarrowedUse,
    env: &'a [UnionTarget],
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
    let Some(expected) = annotation_type(expected_text) else {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_UNKNOWN_ANNOTATION.to_owned(),
            file,
            span,
            message: format!("Cannot find name '{expected_text}'."),
        });
        return None;
    };
    let matching: Vec<&UnionTarget> = env
        .iter()
        .filter(|target| target.name == use_.target)
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
    if target.has_literal_init {
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
    Some(LinkedUse {
        span,
        expected,
        expected_text: expected_text.to_owned(),
        target,
    })
}

/// Refines one linked use through decline regions and applicable guards.
///
/// Unguarded uses diagnose over the full union spelling; every applicable
/// guard must agree on one primitive (see [`narrow_guard`]).
fn refine_use(
    file: FileId,
    use_: &NarrowedUse,
    linked: &LinkedUse<'_>,
    uctx: &mut NarrowUseCtx<'_>,
) {
    let span = linked.span;
    let expected = linked.expected;
    let expected_text = linked.expected_text.as_str();
    let target: &UnionTarget = linked.target;
    let guards = uctx.guards;
    let declines = uctx.declines;
    let report: &mut FileReport = &mut *uctx.report;
    if let Some(region) = declines
        .iter()
        .find(|region| span_contains(region.span, use_.init_span))
    {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!(
                "narrowing declined for use of '{}': {}",
                use_.target, region.reason
            ),
        });
        return;
    }
    let mut narrowed: Vec<Narrowed> = Vec::new();
    for guard in guards.iter().filter(|guard| guard.target == use_.target) {
        // Then of `===` (else of `!==`, after of `!==`) keeps the matched
        // literal; every other branch refines to the complement.
        let side = if span_contains(guard.then_span, use_.init_span) {
            Some(!guard.negated)
        } else if guard
            .else_span
            .is_some_and(|else_span| span_contains(else_span, use_.init_span))
            || guard.early_return && use_.init_span.lo >= guard.if_span.hi
        {
            Some(guard.negated)
        } else {
            None
        };
        let Some(matched_side) = side else {
            continue;
        };
        match narrow_guard(guard, matched_side, target, file, span, report) {
            Ok(narrow) => narrowed.push(narrow),
            Err(()) => return,
        }
    }
    let verdict = if narrowed.is_empty() {
        Narrowed::FullUnion
    } else {
        let first = narrowed[0];
        if narrowed.iter().all(|narrow| *narrow == first) {
            first
        } else {
            report.unsupported.push(UnsupportedDecl {
                file,
                span,
                reason: format!(
                    "overlapping guards refine '{}' differently: outside the subset",
                    use_.target
                ),
            });
            return;
        }
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

/// Parses an object annotation (`{ a: number; b: string }`) into member
/// name/type-text pairs in annotation order.
///
/// Separators follow tsc type literals (`;`, `,`, newlines); only plain
/// identifier names parse. Returns `None` for anything outside the subset
/// (missing braces, unparseable or non-identifier members) — never a
/// verdict. An empty `{}` parses to an empty vec; callers decline it
/// separately because tsc skips excess checks against `{}`.
fn parse_object_annotation(text: &str) -> Option<Vec<(String, String)>> {
    let inner = text.strip_prefix('{')?.strip_suffix('}')?;
    let mut members = Vec::new();
    for piece in inner.split([';', ',', '\n']) {
        let piece = piece.trim();
        if piece.is_empty() {
            continue;
        }
        let (name, ty) = piece.split_once(':')?;
        let name = name.trim();
        let ty = ty.trim();
        if name.is_empty()
            || ty.is_empty()
            || !name
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
        {
            return None;
        }
        members.push((name.to_owned(), ty.to_owned()));
    }
    Some(members)
}

/// Classifies one object member's type text: primitive [`TypeId`], or `None`
/// with a flag saying whether the oracle would call it unknown (`TS2304`)
/// versus out-of-subset (union/complex shapes the solver declines).
fn classify_member_type(ty: &str) -> Result<TypeId, bool> {
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
/// Priority inside the object path mirrors tsc (probed 7.0.2): wrong-member
/// `TS2322`s (literal order, one per member) beat the first-excess `TS2353`,
/// which beats missing members (one `TS2741`, or one `TS2739` for several).
/// Only one family ever fires per declaration.
fn check_one(
    file: FileId,
    node: NodeId,
    decl: &ConstDecl,
    binder: &Binder,
    db: &mut QueryDb,
    freshness: &FreshnessTable,
    report: &mut FileReport,
) {
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
    if annotation.starts_with('{') {
        let mut ctx = CheckCtx {
            file,
            node,
            db,
            freshness,
            report,
        };
        check_object(decl, span, annotation, &mut ctx);
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
    let Some(ann_ty) = annotation_type(annotation) else {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_UNKNOWN_ANNOTATION.to_owned(),
            file,
            span,
            message: format!("Cannot find name '{annotation}'."),
        });
        return;
    };
    // Thread through the memo database: the annotation type is the answer
    // to this declaration's TypeOf query; the dep edge lets a later edit
    // invalidate exactly this entry.
    let key = QueryKey {
        file,
        node,
        kind: QueryKind::TypeOf,
    };
    let dep = Dep { file, node };
    let stored = db.type_of(key, &[dep], || ann_ty);
    debug_assert_eq!(stored, ann_ty);
    if let Some(init_object) = decl.init_object.as_ref() {
        check_primitive_annotation_object_init(file, span, annotation, init_object, report);
        return;
    }
    let Some(init) = decl.init else {
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
/// flat as the subset grows.
struct CheckCtx<'a> {
    file: FileId,
    node: NodeId,
    db: &'a mut QueryDb,
    freshness: &'a FreshnessTable,
    report: &'a mut FileReport,
}

/// Object annotation (`{ a: number; ... }`) against any initializer.
///
/// Member-type failures diagnose unknown names (`TS2304`) or decline the
/// rest (union/complex shapes) before any shape comparison; the shape
/// comparison itself fires exactly one diagnostic family per declaration
/// (wrong > excess > missing). See the module-level object rules.
fn check_object(decl: &ConstDecl, span: Span, annotation: &str, ctx: &mut CheckCtx<'_>) {
    let Some(parsed) = parse_object_members(annotation, span, ctx) else {
        return;
    };
    let Some(expected) = classify_expected(&parsed, span, ctx) else {
        return;
    };
    let expected_text = object_type_text(
        &expected
            .iter()
            .map(|(name, _, _)| name.as_str())
            .collect::<Vec<&str>>(),
        &expected
            .iter()
            .map(|(_, _, ty)| ty.as_str())
            .collect::<Vec<&str>>(),
    );
    finish_object_check(decl, span, &expected, &expected_text, ctx);
}

/// Shared object-literal comparison tail: memoizes the shape, then fires
/// the single-family comparison (or the non-object-init path) with
/// `expected_text` as the expected-type spelling — the `{...}` expansion
/// for inline annotations, the bare interface name for
/// [`check_interface_shape`] (probed tsc 7.0.2: interface elaborations
/// spell the name, never expanded members).
fn finish_object_check(
    decl: &ConstDecl,
    span: Span,
    expected: &[ExpectedMember],
    expected_text: &str,
    ctx: &mut CheckCtx<'_>,
) {
    memoize_object_shape(expected, ctx);
    match decl.init_object.as_ref() {
        None => check_object_annotation_non_object_init(decl, span, expected_text, ctx),
        Some(init_object) => {
            compare_object_members(span, expected, expected_text, init_object, ctx);
        }
    }
}

/// Parses an object annotation into `(name, type-text)` pairs, declining
/// unparseable shapes and empty `{}` (tsc skips excess checks against `{}`).
fn parse_object_members(
    annotation: &str,
    span: Span,
    ctx: &mut CheckCtx<'_>,
) -> Option<Vec<(String, String)>> {
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

/// One classified annotation member: name, primitive type, original text.
type ExpectedMember = (String, TypeId, String);

/// Resolves every member type to a primitive: unknown names diagnose
/// (`TS2304`, one per name), union/complex shapes decline the declaration.
fn classify_expected(
    parsed: &[(String, String)],
    span: Span,
    ctx: &mut CheckCtx<'_>,
) -> Option<Vec<ExpectedMember>> {
    let mut expected: Vec<ExpectedMember> = Vec::with_capacity(parsed.len());
    let mut unknown: Vec<&str> = Vec::new();
    for (name, ty) in parsed {
        match classify_member_type(ty) {
            Ok(id) => expected.push((name.clone(), id, ty.clone())),
            Err(is_unknown) => {
                if is_unknown {
                    unknown.push(ty.as_str());
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
            .map(|(name, id, _)| (name.clone(), *id))
            .collect(),
    };
    let ann_ty = ctx.db.types_mut().intern(shape);
    let key = QueryKey {
        file: ctx.file,
        node: ctx.node,
        kind: QueryKind::TypeOf,
    };
    let dep = Dep {
        file: ctx.file,
        node: ctx.node,
    };
    let stored = ctx.db.type_of(key, &[dep], || ann_ty);
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
            .find(|entry| entry.0.as_str() == name.as_str())
        else {
            continue;
        };
        if kind.type_id() != entry.1 {
            wrong.push((kind.widened_name(), entry.2.as_str()));
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
        .find(|name| expected.iter().all(|entry| entry.0 != *name))
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

/// Missing members (annotation order): one is `TS2741`, several collapse
/// into one `TS2739`.
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
        .map(|(name, _, _)| name.as_str())
        .filter(|name| actual.iter().all(|slot| slot.0 != *name))
        .collect();
    if missing.len() == 1 {
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_MISSING_MEMBER.to_owned(),
            file: ctx.file,
            span,
            message: format!(
                "Property '{}' is missing in type '{actual_text}' but required in type '{expected_text}'.",
                missing[0]
            ),
        });
    } else if !missing.is_empty() {
        ctx.report.diagnostics.push(PithDiagnostic {
            code: CODE_MISSING_MANY.to_owned(),
            file: ctx.file,
            span,
            message: format!(
                "Type '{actual_text}' is missing the following properties from type '{expected_text}': {}",
                missing.join(", ")
            ),
        });
    }
}

/// Object annotation with a non-object initializer.
///
/// Primitive literals diagnose compositionally (oracle: `Type 'number' is
/// not assignable to type '{ a: number; }'.`); missing/non-literal
/// initializers decline with the usual reasons.
fn check_object_annotation_non_object_init(
    decl: &ConstDecl,
    span: Span,
    expected_text: &str,
    ctx: &mut CheckCtx<'_>,
) {
    let Some(init) = decl.init else {
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
/// [`classify_expected`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceMember {
    /// Member name as written.
    pub name: String,
    /// Raw annotation text (`Some("number")`); `None` when absent.
    pub annotation_text: Option<String>,
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDecl {
    /// The declaration (spans/scopes/shapes as in [`check_file`]).
    pub decl: ConstDecl,
    /// Source slice of the initializer span for literal spellings.
    pub init_text: Option<String>,
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
        check_one(
            self.file,
            self.node,
            self.decl,
            self.binder,
            &mut *self.db,
            self.freshness,
            &mut *self.report,
        );
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
    {
        route.delegate();
        return;
    }
    let span = binder_span(route.binder, route.file, decl);
    route.resolve_shape(span, annotation);
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
    if decl.init.is_some() && decl.init_object.is_some() {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: "contradictory initializer facts: primitive kind with object members"
                .to_owned(),
        });
        return;
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
        return;
    }
    if shape.has_type_params {
        ctx.report.unsupported.push(UnsupportedDecl {
            file: ctx.file,
            span,
            reason: format!("generic interface '{}' is outside the subset", shape.name),
        });
        return;
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
        parsed.push((member.name.clone(), text.to_owned()));
    }
    let Some(expected) = classify_expected(&parsed, span, ctx) else {
        return;
    };
    finish_object_check(decl, span, &expected, annotation, ctx);
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
    let mut freshness = FreshnessTable::default();
    for (index, decl) in decls.iter().enumerate() {
        if let Some(init) = decl.decl.init_object.as_ref() {
            freshness
                .fresh
                .insert((file, occurrence_node(index)), init.fresh);
        }
    }
    let mut report = FileReport::default();
    for (index, decl) in decls.iter().enumerate() {
        let mut route = EnumDeclCtx {
            file,
            node: occurrence_node(index),
            decl,
            input,
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
struct EnumDeclCtx<'a, 'b> {
    file: FileId,
    node: NodeId,
    decl: &'a EnumDecl,
    input: &'a EnumInput<'b>,
    binder: &'a Binder,
    db: &'a mut QueryDb,
    freshness: &'a FreshnessTable,
    report: &'a mut FileReport,
}

impl EnumDeclCtx<'_, '_> {
    /// Plain spellings (and missing annotations) keep [`check_one`]'s
    /// verdicts by construction.
    fn delegate(&mut self) {
        check_one(
            self.file,
            self.node,
            &self.decl.decl,
            self.binder,
            &mut *self.db,
            self.freshness,
            &mut *self.report,
        );
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
    /// the full name, namespaces diagnose `PITH2709`, the rest decline.
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
            self.unsupported(
                span,
                format!(
                    "annotation '{annotation}' is not an enum or interface: outside the subset"
                ),
            );
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
            InitKind::Null | InitKind::Undefined => {
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
fn route_enum_declaration(route: &mut EnumDeclCtx<'_, '_>) {
    let annotation = route.decl.decl.annotation.as_deref().map(str::trim);
    let Some(annotation) = annotation else {
        route.delegate();
        return;
    };
    if annotation.starts_with('{')
        || annotation.contains('|')
        || annotation_type(annotation).is_some()
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
            span: span(0, 1),
            complex_reason: Some("method signature 'run' is outside the subset".to_owned()),
        });
        let mut generic = interface_shape(&binder, "G", 0, vec![("a", "number")]);
        generic.has_type_params = true;
        let mut method = interface_shape(&binder, "M", 0, vec![("a", "number")]);
        method.members.push(InterfaceMember {
            name: "run".to_owned(),
            annotation_text: None,
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
                ..decl("a", 0, 10, "number", InitKind::Number)
            },
            ConstDecl {
                kind: DeclKind::Let,
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
            ("v", span(36, 44)),
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
        let unparseable = object_decl(
            "v",
            36,
            44,
            "{ a?: number }",
            vec![("a", ObjectMemberKind::Number)],
        );
        let decls = [union, nested, non_literal_member, empty, unparseable];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 5);
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
        let names: Vec<&str> = parsed.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, ["a", "b", "c", "d"]);
        assert_eq!(
            parse_object_annotation("{ a: number; }")
                .expect("parses")
                .len(),
            1
        );
        assert!(parse_object_annotation("{}").expect("parses").is_empty());
        for bad in [
            "number",
            "{ a }",
            "{ 'a': number }",
            "{ a?: number }",
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
            return_annotation: annotation.map(str::to_owned),
            body,
        }
    }

    fn single(kind: InitKind) -> FunctionBody {
        FunctionBody::SingleReturn(FunctionReturn {
            kind: Some(kind),
            init_object: None,
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
        })
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
        // Overloads (or shadowing the fact set cannot disambiguate): no
        // speculative resolution, one unsupported note.
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

    #[test]
    fn call_param_gates_are_unsupported_never_silent() {
        let binder = calls_binder(&[], &[]);
        let mut unannotated = callable("u", vec![("v", "number")]);
        unannotated.params[0].annotated = false;
        unannotated.params[0].annotation = None;
        let mut optional = callable("o", vec![("b", "number")]);
        optional.params[0].optional = true;
        let mut rest = callable("r", vec![("items", "number[]")]);
        rest.params[0].is_rest = true;
        let union = callable("n", vec![("v", "number | string")]);
        let unknown = callable("w", vec![("v", "Nope")]);
        let mut complex = callable("c", vec![("v", "number")]);
        complex.params_complex = true;
        let decls = [unannotated, optional, rest, union, unknown, complex];
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
            reasons[1].contains("optional parameter"),
            "reason: {}",
            reasons[1]
        );
        assert!(
            reasons[2].contains("rest parameter"),
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
                return_annotation: ret_ann.map(str::to_owned),
                body,
            },
            type_params: t_params.iter().map(|param| (*param).to_owned()).collect(),
            type_params_complex: false,
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

    #[test]
    fn generic_multi_param_declines_and_skips_call() {
        // `pair<T, U>`: the declaration declines; its call skips silently
        // (the declaration note covers it — no double-report).
        let binder = binder_with(&[("pair", span(0, 20))]);
        let mut decl = identity_decl(0, 20);
        decl.decl.name = "pair".to_owned();
        decl.type_params = vec!["T".to_owned(), "U".to_owned()];
        let calls = [generic_call_args(
            "pair",
            30,
            34,
            vec![(InitKind::Number, 40, 41)],
            None,
        )];
        let report = generics_report(&[decl], &calls, &binder);
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
    fn generic_complex_type_params_decline() {
        // Constraints/defaults/modifiers arrive as one flag: one reason.
        let binder = binder_with(&[("id", span(0, 20))]);
        let mut decl = identity_decl(0, 20);
        decl.type_params_complex = true;
        let report = generics_report(&[decl], &[], &binder);
        assert!(report.diagnostics.is_empty());
        assert_eq!(report.unsupported.len(), 1);
        assert!(
            report.unsupported[0].reason.contains("constraint"),
            "reason: {}",
            report.unsupported[0].reason
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
            },
            init_text: text.map(str::to_owned),
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
}
