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
//! Out-of-subset declarations (union annotations, missing annotations,
//! non-literal or missing initializers, union/complex member types, empty
//! `{}` annotations, stale-literal excess candidates, contradictory
//! primitive/object initializer pairs) are recorded as [`UnsupportedDecl`]
//! entries, never silently dropped.
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
    memoize_object_shape(&expected, ctx);
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
    match decl.init_object.as_ref() {
        None => check_object_annotation_non_object_init(decl, span, &expected_text, ctx),
        Some(init_object) => {
            compare_object_members(span, &expected, &expected_text, init_object, ctx);
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
}
