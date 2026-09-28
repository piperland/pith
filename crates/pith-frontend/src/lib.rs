//! Pith frontend adapter (Oxc boundary).
//!
//! Provenance: Oxc 0.152.0 (MIT), oxc-project/oxc. Re-checked 2026-09-28:
//! 0.152.0 is still the latest 0.15x on crates.io, so no bump. Exact `=`
//! pins + Cargo.lock committed.
//!
//! Boundary law: everything Oxc-typed dies inside [`parse_module`]. Callers
//! receive only Pith-owned facts keyed by [`FileId`]. No `oxc_*` type may
//! appear in any other `pith-*` crate's public API.
//!
//! Declaration facts (P010): [`ParsedFile::decls`] carries one [`DeclFact`]
//! per `const` declarator with a simple identifier binding, pairing the
//! annotation text and span ([`AnnotationFact`]) with the initializer
//! literal kind and span ([`InitFact`]/[`InitKind`]). Each fact keys to its
//! owning [`SymbolFact`] by per-file symbol index. These replace the
//! solver's hand-fed `ConstDecl` seam (the `DeclAnnotationFact` plus
//! `InitLiteralFact` BLOCKER in `pith-solver`).
//!
//! Build-mode decision (P010): the declarator walk uses
//! `oxc_ast_visit::Visit` over the already-parsed program — NOT
//! `SemanticBuilder::with_build_nodes(true)`. Rationale: declarators are
//! purely syntactic, so the visitor reaches every one (top level, nested
//! blocks/functions, `export const`, `for(const ... of ...)`) with a single
//! O(n) pass and zero change to the semantic build; enabling `AstNodes`
//! would materialize a node arena plus parent maps for every file just to
//! rediscover the same declarators. Measurement: no local Rust toolchain is
//! available to this task (CTO verifies remotely on E2B), so the
//! with/without-`AstNodes` semantic-build delta is recorded as unknown; the
//! semantic-build configuration is unchanged by this task, and the added
//! cost is one linear visitor pass. Destructured bindings (`const {a} = …`)
//! bind many symbols per declarator and are skipped — outside the solver
//! subset, never silently mis-keyed.
//!
//! Function facts (P013): [`ParsedFile::functions`] carries one
//! [`FunctionFact`] per named `function` declaration (including
//! `export function` and overload signatures, plus `declare function`).
//! Linkage reuses the `(name, binding start)` symbol keying and
//! declarator-scope threading of [`DeclFact`]. Each fact records identifier
//! parameter names with their annotated-ness ([`FunctionParamFact`]; names
//! only — patterns that are not plain identifiers set `params_complex`
//! instead of mis-keying), the return annotation text + span
//! ([`AnnotationFact`], `None` when unannotated), and the body shape
//! ([`FunctionBodyFact`]). Only straight-line single-`return` bodies with an
//! argument are checkable: their literal kind + span (plus member facts for
//! returned `{ ... }` literals) feed the solver; bodies without a node are
//! [`FunctionBodyFact::NoBody`], statement-less bodies are
//! [`FunctionBodyFact::Empty`], and everything else (multiple returns,
//! branches, loops, bare or missing `return`) is
//! [`FunctionBodyFact::Complex`] for the solver to decline. Out of scope, no
//! facts: function expressions, arrow functions, object and class methods,
//! accessors, constructors. Anonymous `export default function …` has no
//! binding and is skipped. `this` parameters are not listed in `params`;
//! parenthesized returns (`return (1)`) classify
//! [`ReturnKind::NonLiteral`], exactly like const initializers; directives
//! do not count as statements for [`FunctionBodyFact::Empty`].
//!
//! Call facts (P014): [`ParsedFile::calls`] carries one [`CallFact`] per
//! direct `f(...)` call expression, in visitor (pre-order) order. Each fact
//! records the callee name plus its identifier span ([`CallFact::callee_span`]),
//! the whole call span ([`CallFact::span`]), and one [`CallArgFact`] per
//! argument (literal kind via [`CallArgKind`] plus span). Only plain
//! `Identifier` callees emit facts: method/member calls (`obj.m()`), optional
//! chains (`f?.()`), and calls with any spread element (`f(...xs)`) are
//! documented non-emissions — out of the solver subset, never mis-recorded.
//! (`super(...)`, `import(...)`, `new f()`, and tagged templates never reach
//! the call visitor as identifier calls.) Nested calls each emit their own
//! fact (`f(g(1))` yields one for `g(1)` and one for `f(...)`, the inner
//! argument classifying [`CallArgKind::NonLiteral`]).
//!
//! Probe basis (tsc 7.0.2 `--strict --pretty false`, recorded in the solver
//! docs): `TS2554` (`Expected 2 arguments, but got 1.`, too-few anchored at
//! the callee, too-many at the first excess argument) beats `TS2345`
//! (`Argument of type 'string' is not assignable to parameter of type
//! 'number'.`, anchored at the argument) — one diagnostic per call site, and
//! only the first mismatched argument reports. Optional/rest arities
//! (`Expected 1-2 arguments …`, `TS2555`) and overload failures (`TS2769`)
//! are declined by the solver; unresolved callees are already tracked as
//! [`UnresolvedFact`]s, so the solver does not double-report them.
//!
//! Parameter enabling (P014, entailed by the call checker): each
//! [`FunctionParamFact`] additionally carries its annotation text plus
//! `optional`/`is_rest` markers. Exact-arity checking needs to decline range
//! (`b?: number`, defaulted) and variadic (`...rest`) lists, and arg-type
//! checking needs the annotated names — none of which name-only params can
//! express. No other declaration-fact surface changes.
//!
//! Guard facts (P015): [`ParsedFile::guards`] carries one [`TypeofGuardFact`]
//! per top-level `if (typeof x === "<lit>")` / `if (typeof x !== "<lit>")`
//! statement, pairing the target identifier plus matched literal with the
//! then/else statement spans that bound each refinement region. The
//! early-return shape (`if (typeof x !== "<lit>") return;`, with `return
//! <expr>;`, `throw`, and single-statement-block variants) sets
//! [`TypeofGuardFact::early_return`]: the code after the statement refines.
//! Everything else emits no guard fact, never a wrong one: `==`/`!=`,
//! compound conditions, non-typeof tests, non-identifier/non-literal operands,
//! and `else if` chains land in [`ParsedFile::decline_regions`] as
//! [`DeclineRegionFact`]s (whole-statement spans with reasons), as do guards
//! nested inside another `if`'s branches and function bodies nested inside
//! another function (narrowing does not cross closures — probed tsc 7.0.2: a
//! use inside a nested closure sees the full union). Loops need no regions:
//! `const` targets cannot be reassigned, so straight-line refinement stays
//! sound inside loop bodies.
//!
//! Type-parameter facts (P016): each [`FunctionFact`] additionally carries
//! its declared type-parameter names in source order ([`TypeParamFact`],
//! empty for non-generic functions). Only plain names feed the solver: any
//! parameter with a constraint (`<T extends string>`), a default
//! (`<T = number>`), or a variance/`const` modifier (`in`/`out`/`const T`)
//! sets `type_params_complex` instead of mis-keying, and the solver declines
//! those declarations (plus multi-parameter lists and nested `T` positions)
//! with reasons. No other generic syntax facts: call-site type arguments,
//! type references, and variance positions are out of scope.
//!
//! Interface facts (P017): [`ParsedFile::interfaces`] carries one
//! [`InterfaceFact`] per `interface` declaration (including `export` and
//! `declare` forms), in visitor (pre-order) order. Each fact links its own
//! [`SymbolFact`] exactly like [`DeclFact`] (per-file index plus owning
//! scope) and records member facts ([`InterfaceMemberFact`]: name plus
//! colon-stripped annotation text) in source order. Only plain non-optional
//! properties with identifier keys feed the solver: methods, index/call/
//! construct signatures, optional members, computed or non-identifier keys,
//! and missing annotations each carry a `complex_reason` instead of
//! mis-keying, and the solver declines those interfaces with per-member
//! reasons. Heritage clauses record parent names
//! ([`InterfaceHeritageFact`]) and generic parameter lists set
//! `has_type_params`; both decline solver-side. `readonly` needs no flag:
//! it never affects literal assignability (probed tsc 7.0.2: clean when
//! members match, plain `TS2322` when wrong).
//!
//! Merge note (P005 law): oxc pre-merges same-scope redeclarations, so
//! `interface Foo {}` plus `const Foo = …` surfaces as ONE [`SymbolFact`]
//! (flags OR-ed, span at the first declaration — read off the oxc 0.152.0
//! `declare_symbol`/`check_redeclaration` sources: `InterfaceExcludes`
//! never intersects value flags, and only `var` redeclarations error).
//! The interface fact links that merged symbol; the const declarator finds
//! no exact `(name, start)` key and emits no [`DeclFact`] — drivers resolve
//! merged spans through the binder instead (see the solver's interface
//! driver, which pins first-declaration anchoring in tests).
//!
//! Enum facts (P018): [`ParsedFile::enums`] carries one [`EnumFact`] per
//! `enum` declaration (including `export`, `const`, and `declare` forms), in
//! visitor (pre-order) order. Symbol linkage reuses the `(name, binding
//! start)` keying of [`DeclFact`]. Each fact records member facts
//! ([`EnumMemberFact`]: name plus [`EnumValueKind`]) in source order.
//! Literal values only — const-eval stays minimal: numeric and string
//! initializers record their values, while every other shape (identifiers,
//! unary/binary expressions, member accesses, template literals, …) records
//! [`EnumValueKind::Computed`] with a reason, so the solver declines those
//! enums instead of mis-checking them. Missing initializers auto-increment
//! (`Red, Green` is `0, 1`; `A = 5, B` is `5, 6`): the first defaults to
//! `0`, later ones to one past the previous NUMERIC member; after a string
//! or computed member (or a computed member name) the increment is
//! unknowable, so the member is computed with a reason. Identifier and
//! string-literal member names record verbatim; computed names decline the
//! member. `const` enums behave identically for checking (probed tsc 7.0.2),
//! so [`EnumFact::is_const`] is recorded only. Ambient (`declare`) enums
//! accept every literal in tsc (probed 7.0.2), so the solver declines them —
//! recorded via [`EnumFact::declared`], never skipped.
//!
//! Namespace facts (P018): [`ParsedFile::namespaces`] carries one
//! [`NamespaceFact`] per `namespace`/`module` block (including `export` and
//! `declare` forms; `module Foo {}` and `namespace Foo {}` behave
//! identically for checking, probed tsc 7.0.2), in visitor (pre-order)
//! order. Declarations inside are visited normally — consts, functions,
//! interfaces, enums, and nested namespaces gain their real scopes, symbols,
//! and facts — so the namespace body is a genuine scope container. Each
//! fact links its own [`SymbolFact`] like [`DeclFact`] and records
//! `body_scope`: the per-file scope index of the `TsModuleBlock` scope
//! (resolved post-pass as the child of the owning scope holding
//! span-contained member symbols; `u32::MAX` when indeterminable, e.g.
//! empty blocks), which lets qualified `NS.Member` annotations resolve
//! through binder scopes. `exported` (on enums, interfaces, and namespaces)
//! records whether the declaration sat under an `export` wrapper: only
//! exported members are visible through qualification in tsc (probed 7.0.2:
//! `NS.Hidden` diagnoses `TS2694` exactly like `NS.Nope`), except inside
//! ambient (`declare`) namespaces, where every member is visible (probed
//! tsc 7.0.2). [`NamespaceFact::exported_members`] additionally names every
//! directly exported member (consts, lets/vars, functions, classes, type
//! aliases, and nested blocks included), so the solver tells hidden members
//! (`TS2694`) apart from exported non-types (declined — kind is unknowable
//! without value facts). `export { E }` specifier lists are not wrappers,
//! so members exported only that way record `exported: false` and list
//! nowhere (documented limit).
//!
//! Probe basis (tsc 7.0.2 `--strict --pretty false`, recorded in the solver
//! docs): simple `===`/`!==` typeof guards refine (then/else/after per
//! negation), `==` narrows identically but is declined (subset pins
//! `===`/`!==`), union members spell canonically
//! (`string | number | boolean | null | undefined`, source order ignored),
//! guard literals outside the union narrow to `never` (silent uses — the
//! solver declines those regions), and literal-initialized `const`s do not
//! narrow at all.

use oxc_allocator::Allocator;
use oxc_ast::ast::{
    Argument, ArrowFunctionExpression, BindingPattern, CallExpression, Class, ExportDeclaration,
    ExportDefaultDeclaration, Expression, Function, FunctionBody, FunctionType, IfStatement,
    ObjectPropertyKind, Program, PropertyKey, PropertyKind, Statement, TSEnumDeclaration,
    TSEnumMemberName, TSInterfaceDeclaration, TSNamespaceDeclaration, TSPropertySignature,
    TSSignature, TSTypeAliasDeclaration, TSTypeAnnotation, VariableDeclaration,
    VariableDeclarationKind, VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{ScopeFlags, SemanticBuilder};
use oxc_span::{GetSpan, SourceType};
use oxc_syntax::operator::{BinaryOperator, UnaryOperator};
use pith_ids::{FileId, Span};

/// Saturating `usize` -> `u32` for per-file fact indices (files never approach
/// 4B facts; saturation beats silent truncation).
#[inline]
#[must_use]
fn sat_u32(v: usize) -> u32 {
    u32::try_from(v).unwrap_or(u32::MAX)
}

/// One lexical scope, indexed per file (position in [`ParsedFile::scopes`]).
#[derive(Clone, Debug)]
pub struct ScopeFact {
    /// Per-file scope index; root scope is always index 0.
    pub index: u32,
    /// Parent scope index, or `u32::MAX` for the root.
    pub parent: u32,
    /// Raw `ScopeFlags` bits (opaque to Pith core; interpreted at boundary).
    pub flags: u32,
}

/// One bound symbol, indexed per file (position in [`ParsedFile::symbols`]).
#[derive(Clone, Debug)]
pub struct SymbolFact {
    /// Per-file symbol index.
    pub index: u32,
    /// Owning scope (per-file scope index).
    pub scope: u32,
    pub name: String,
    pub span: Span,
    /// Raw `SymbolFlags` bits.
    pub flags: u32,
    /// Number of resolved references (spans deferred; see gap note below).
    pub resolved_ref_count: u32,
    /// Names of resolved references (debug/audit aid).
    pub resolved_ref_names: Vec<String>,
}

/// Unresolved (global or undeclared) reference name + occurrence count.
#[derive(Clone, Debug)]
pub struct UnresolvedFact {
    pub name: String,
    pub count: u32,
}

/// Import specifier with its span.
#[derive(Clone, Debug)]
pub struct ImportFact {
    pub specifier: String,
    pub span: Span,
}

/// Annotation on one `const` declarator: raw type text plus its span.
///
/// `span` is the raw `TSTypeAnnotation` range (colon-inclusive: `: number`
/// spans the colon through the type). `text` is the source slice of that
/// range with the leading colon stripped (`"number"`, `"number | string"`),
/// so it feeds the solver's annotation map (and its `'|'` union check)
/// directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AnnotationFact {
    pub text: String,
    pub span: Span,
}

/// Initializer literal kind, mirroring the solver's subset.
///
/// Only primitive literals are classifiable. Anything else (`other`,
/// `{...}`, `f()`, `` `tpl` ``, `-1`, …) is [`InitKind::NonLiteral`] —
/// expression facts the adapter does not emit yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitKind {
    /// A numeric literal (`1`, `0x10`, …).
    Number,
    /// A string literal (`"ok"`, …).
    String,
    /// `true` / `false`.
    Boolean,
    /// `null`.
    Null,
    /// The `undefined` identifier.
    Undefined,
    /// Any non-literal initializer (identifier, object, call, …).
    NonLiteral,
}

/// Initializer on one `const` declarator: literal kind plus span.
///
/// `span` is the initializer expression's own range (`None` on
/// [`DeclFact::init`] means no initializer at all, e.g. `declare const`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InitFact {
    pub kind: InitKind,
    pub span: Span,
}

/// One `const` declarator's declaration facts, keyed to its symbol.
///
/// `symbol` is the per-file index into [`ParsedFile::symbols`] of the
/// [`SymbolFact`] for the same declarator (matched on binding name +
/// binding start; declaration order in [`ParsedFile::decls`] is source
/// order). `scope` redundantly carries that symbol's owning scope so
/// downstream drivers resolve spans without re-indexing into `symbols`
/// (P012 scope threading). Only simple-identifier bindings produce facts;
/// destructured declarators are skipped (see the module-level build-mode note).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclFact {
    /// Per-file symbol index of the declarator's binding.
    pub symbol: u32,
    /// Owning scope (per-file scope index) of [`DeclFact::symbol`].
    pub scope: u32,
    /// Raw annotation text + span; `None` means unannotated.
    pub annotation: Option<AnnotationFact>,
    /// Initializer literal kind + span; `None` means no initializer.
    pub init: Option<InitFact>,
}

/// One `function` declaration's declaration facts, keyed to its symbol.
///
/// `symbol`/`scope` link exactly like [`DeclFact`]: the per-file index of
/// the [`SymbolFact`] for the function name (matched on name + binding
/// start) plus that symbol's owning scope. Overload signatures merge into
/// the first declaration's symbol, so every overload of one name shares one
/// symbol index (diagnostics anchor at the first declaration — a documented
/// precision limit, never a silent skip). Only named declarations produce
/// facts (see the module-level scope note).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionFact {
    /// Per-file symbol index of the function name binding.
    pub symbol: u32,
    /// Owning scope (per-file scope index) of [`FunctionFact::symbol`].
    pub scope: u32,
    /// Identifier parameters in source order, up to the first
    /// unrepresentable pattern (see `params_complex`).
    pub params: Vec<FunctionParamFact>,
    /// `true` when the parameter list holds a pattern no name can represent
    /// (destructured or non-identifier rest): `params` is then a prefix and
    /// the solver declines instead of checking it.
    pub params_complex: bool,
    /// Declared type-parameter names in source order (empty for non-generic
    /// functions). Names record even when `type_params_complex` (the solver
    /// declines on the flag, never on a miscount).
    pub type_params: Vec<TypeParamFact>,
    /// `true` when any type parameter carries a constraint, a default, or
    /// an `in`/`out`/`const` modifier: the solver declines instead of
    /// instantiating it.
    pub type_params_complex: bool,
    /// Raw return annotation text + span; `None` means unannotated.
    pub return_annotation: Option<AnnotationFact>,
    /// Body shape; only [`FunctionBodyFact::SingleReturn`] is checkable.
    pub body: FunctionBodyFact,
}

/// One declared type parameter: its name as written (`T` in `id<T>`).
///
/// Only the name crosses the boundary (sliced off the parameter's binding
/// span, exactly like value-parameter names). Constraints, defaults, and
/// modifiers never become facts — any one of them sets
/// [`FunctionFact::type_params_complex`] instead.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeParamFact {
    /// Type-parameter name as written.
    pub name: String,
}

/// One identifier parameter: its name plus whether it carries a type
/// annotation.
///
/// `annotated` is what the return checker gates on (unannotated parameters
/// are outside the subset); `annotation_text`/`optional`/`is_rest` feed the
/// call-site checker (P014): arg-type checks need the annotated names, and
/// exact-arity checks decline range (`b?: number`, defaulted `b: T = …`) and
/// variadic (`...rest: T[]`) lists instead of mis-counting them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionParamFact {
    /// Parameter name as written.
    pub name: String,
    /// Whether the parameter carries a type annotation.
    pub annotated: bool,
    /// Raw annotation text (`Some("number")`); `None` when unannotated.
    pub annotation_text: Option<String>,
    /// `true` for `b?: number` and defaulted `b: T = …` (arity is a range).
    pub optional: bool,
    /// `true` for `...rest: T[]` (variadic).
    pub is_rest: bool,
}

/// Literal kind of a straight-line `return <expr>;`, mirroring [`InitKind`].
///
/// A separate type so the boolean payload rides along: tsc spells fresh
/// boolean members literally (`{ done: false; }`) in missing-member
/// elaborations while every other kind widens, so return-object member
/// facts need the value (same probe as the const object subset).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReturnKind {
    /// A numeric literal (`1`, `0x10`, …).
    Number,
    /// A string literal (`"ok"`, …).
    String,
    /// `true` / `false` (payload is the literal value).
    Boolean(bool),
    /// `null`.
    Null,
    /// The `undefined` identifier.
    Undefined,
    /// Any non-literal return (identifier, call, parenthesized, …).
    NonLiteral,
}

/// One `{ ... }` member of a returned object literal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnMemberFact {
    /// Member name (identifier keys only; anything else makes the body
    /// [`FunctionBodyFact::Complex`]).
    pub name: String,
    /// Literal kind of the member value.
    pub kind: ReturnKind,
    /// Span of the member value expression.
    pub span: Span,
}

/// A straight-line `return <expr>;`: literal kind + span, plus member facts
/// when the returned expression is an object literal (literal order).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SingleReturnFact {
    /// Literal kind of the returned expression (`NonLiteral` for object
    /// literals, whose shape lives in `members`).
    pub kind: ReturnKind,
    /// Span of the returned expression.
    pub span: Span,
    /// Member facts iff the returned expression is `{ ... }`.
    pub members: Option<Vec<ReturnMemberFact>>,
}

/// Body shape of one function declaration.
///
/// Only [`FunctionBodyFact::SingleReturn`] feeds the solver; every other
/// shape declines to a solver `UnsupportedDecl` with a distinct reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionBodyFact {
    /// Exactly one statement, `return <expr>;` with an argument.
    SingleReturn(SingleReturnFact),
    /// No body node: `declared` tells `declare function` apart from an
    /// overload signature.
    NoBody {
        /// `true` for `declare function` (ambient, never has a body).
        declared: bool,
    },
    /// A body with no statements (directives do not count).
    Empty,
    /// Anything else: multiple returns, branches, loops, bare or missing
    /// `return`, spreads/methods/computed keys in a returned literal.
    Complex,
}

/// Argument literal kind at a direct call site, mirroring [`InitKind`].
///
/// Only primitive literals classify; everything else (identifiers, objects,
/// calls, templates, `-1`, …) is [`CallArgKind::NonLiteral`] — expression
/// facts the adapter does not emit yet. Deliberately payload-free: tsc's
/// `TS2345` elaborations spell widened names only (probed 7.0.2), so the
/// boolean value rides nowhere.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CallArgKind {
    /// A numeric literal (`1`, `0x10`, …).
    Number,
    /// A string literal (`"ok"`, …).
    String,
    /// `true` / `false`.
    Boolean,
    /// `null`.
    Null,
    /// The `undefined` identifier.
    Undefined,
    /// Any non-literal argument (identifier, object, call, …).
    NonLiteral,
}

/// One argument of a direct call: literal kind plus span.
///
/// `span` is the argument expression's own range, so the solver anchors
/// `TS2345`-family diagnostics at the mismatched argument exactly like tsc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallArgFact {
    /// Literal kind of the argument expression.
    pub kind: CallArgKind,
    /// Span of the argument expression.
    pub span: Span,
}

/// One direct `f(...)` call's call-site facts.
///
/// `callee_span` is the callee identifier's own range (too-few-arity
/// diagnostics anchor here, mirroring tsc); `span` is the whole call
/// expression's range. `args` is source order, one fact per argument —
/// including non-literals (the solver skips those per-argument, never the
/// whole call, so arity still checks).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallFact {
    /// Callee name as written.
    pub callee: String,
    /// Span of the callee identifier.
    pub callee_span: Span,
    /// Span of the whole call expression.
    pub span: Span,
    /// Argument facts in source order.
    pub args: Vec<CallArgFact>,
}

/// One straight-line `typeof` guard: `if (typeof x === "<lit>")` or
/// `if (typeof x !== "<lit>")` at the top level of its statement list (never
/// nested inside another `if`'s branches — those decline instead).
///
/// Only simple identifier-plus-string-literal comparisons emit facts: either
/// operand order qualifies, and one layer of parentheses around the whole
/// condition is transparent. Anything else (non-identifier targets,
/// non-literal comparands, `==`, compound conditions, `else if` chains)
/// emits no fact here — the statement lands in
/// [`ParsedFile::decline_regions`] instead, never mis-recorded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeofGuardFact {
    /// Target name as written in `typeof <target>`.
    pub target: String,
    /// Span of the target identifier occurrence.
    pub target_span: Span,
    /// Matched literal text (`"string"` for `typeof x === "string"`).
    pub matched: String,
    /// `true` for `!==` (regions flip), `false` for `===`.
    pub negated: bool,
    /// Statement span of the then branch (refines to `matched` for `===`).
    pub then_span: Span,
    /// Statement span of a plain `else` branch (refines to the complement);
    /// `None` when absent (`else if` chains never reach facts — declined).
    pub else_span: Option<Span>,
    /// The exact early-exit shape with no `else`: the then branch diverges
    /// (bare/valued `return`, `throw`, directly or in a single-statement
    /// block), so the code after the statement refines (to `matched` for
    /// `!==`, to the complement for `===`).
    pub early_return: bool,
    /// Whole `if` statement span (bounds the after-region when
    /// [`TypeofGuardFact::early_return`]).
    pub if_span: Span,
}

/// One statement span the narrowing subset refuses to reason inside.
///
/// Covers non-simple guard conditions, `else-if` chains, guards nested inside
/// another guard's branches, and function bodies nested inside another
/// function (closures reset narrowing — probed tsc 7.0.2). The solver
/// declines identifier-uses inside these spans with the recorded reason
/// instead of verdicting. Literal-initializer declarations inside are
/// unaffected (they check as usual — only narrowing consults regions).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclineRegionFact {
    /// Whole-statement span (the `if` statement, or the nested function).
    pub span: Span,
    /// Why narrowing declines here.
    pub reason: String,
}

/// One member of an `interface` declaration: its name plus its annotation.
///
/// Checkable members (plain non-optional properties with identifier keys)
/// carry the colon-stripped annotation text verbatim (`Some("number")`);
/// the solver classifies it into primitives (checked), unknown names
/// (`TS2304`, mirroring the object path), or union/complex shapes
/// (declined). Anything structural the subset cannot spell — methods,
/// index/call/construct signatures, optional members, computed or
/// non-identifier keys, missing annotations — carries a `complex_reason`
/// instead, so the solver declines with a per-member reason, never a
/// forced verdict. `readonly` is not structural: those members stay
/// checkable (assignability ignores it — probed tsc 7.0.2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceMemberFact {
    /// Member name as written (identifier keys verbatim; sliced key text
    /// for computed keys; the parameter name for index signatures; fixed
    /// descriptors (`"call signature"`) for keyless shapes).
    pub name: String,
    /// Colon-stripped annotation text; `None` when absent or keyless.
    pub annotation_text: Option<String>,
    /// Span of the whole member signature.
    pub span: Span,
    /// Why this member is outside the subset; `None` when checkable.
    pub complex_reason: Option<String>,
}

/// One heritage parent of an `interface` declaration: name plus span.
///
/// Names feed decline reasons only — heritage is outside the subset, so no
/// verdict ever reads them. An unsliceable parent name (only possible with
/// recovery from parse errors) records `""` rather than dropping the
/// clause: the non-empty fact still declines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceHeritageFact {
    /// Parent name as written (`"Base"`, `"A.B"` for qualified names).
    pub name: String,
    /// Span of the heritage clause.
    pub span: Span,
}

/// One `interface` declaration's declaration facts, keyed to its symbol.
///
/// `symbol`/`scope` link exactly like [`DeclFact`]: the per-file index of
/// the [`SymbolFact`] for the interface name (matched on name + binding
/// start) plus that symbol's owning scope. Merged pairs (`interface Foo`
/// plus `const Foo`) share one symbol — the interface fact links it; the
/// const emits no [`DeclFact`] (see the module-level merge note).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InterfaceFact {
    /// Per-file symbol index of the interface name binding.
    pub symbol: u32,
    /// Owning scope (per-file scope index) of [`InterfaceFact::symbol`].
    pub scope: u32,
    /// Interface name as written.
    pub name: String,
    /// Span of the whole declaration.
    pub span: Span,
    /// Member facts in source order.
    pub members: Vec<InterfaceMemberFact>,
    /// Heritage parents; non-empty declines solver-side.
    pub heritage: Vec<InterfaceHeritageFact>,
    /// `true` when the interface declares type parameters: the solver
    /// declines instead of instantiating them.
    pub has_type_params: bool,
    /// Whether the declaration sat under an `export` wrapper. Only exported
    /// members are visible through namespace qualification (except inside
    /// ambient namespaces); top-level uses ignore the flag.
    pub exported: bool,
}

/// One member of an `enum` declaration: its constant value, when computable
/// without full const-eval.
///
/// Numeric and string initializers record their values; everything else
/// (identifiers, unary/binary expressions, member accesses, …) is
/// [`EnumValueKind::Computed`] with a reason, so the solver declines those
/// enums instead of mis-checking them. Missing initializers auto-increment
/// past the previous numeric member (`0` for the first); after a string or
/// computed member the increment is unknowable and also computed.
#[derive(Clone, Debug, PartialEq)]
pub enum EnumValueKind {
    /// A numeric literal initializer (`1`, `0x10`, …): the parsed value.
    Number(f64),
    /// A string literal initializer (`"a"`, …): the unescaped value.
    String(String),
    /// Any non-literal initializer, missing increment base, or computed
    /// member name: the solver declines enums holding one of these.
    Computed {
        /// Why no value is recorded (e.g. `"non-literal initializer"`).
        reason: String,
    },
}

/// One `enum` member: its name plus its constant value, if computable.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumMemberFact {
    /// Member name as written (identifier and string-literal names verbatim;
    /// sliced key text for computed names, which always decline).
    pub name: String,
    /// Constant value, or the decline reason when uncomputable.
    pub value: EnumValueKind,
    /// Span of the whole member (`A = 1`, name included).
    pub span: Span,
}

/// One `enum` declaration's declaration facts, keyed to its symbol.
///
/// `symbol`/`scope` link exactly like [`DeclFact`]: the per-file index of
/// the [`SymbolFact`] for the enum name (matched on name + binding start)
/// plus that symbol's owning scope. Merged pairs (`enum A { X }` plus
/// `enum A { Y }`) share one symbol — each declaration links it with its
/// own member list; the solver declines ambiguous multi-shape enums.
#[derive(Clone, Debug, PartialEq)]
pub struct EnumFact {
    /// Per-file symbol index of the enum name binding.
    pub symbol: u32,
    /// Owning scope (per-file scope index) of [`EnumFact::symbol`].
    pub scope: u32,
    /// Enum name as written.
    pub name: String,
    /// Span of the whole declaration.
    pub span: Span,
    /// Member facts in source order.
    pub members: Vec<EnumMemberFact>,
    /// `true` for `const enum`: checking is identical (probed tsc 7.0.2),
    /// so the flag is recorded only.
    pub is_const: bool,
    /// `true` for `declare enum` (ambient): tsc accepts every literal, so
    /// the solver declines instead of verifying.
    pub declared: bool,
    /// Whether the declaration sat under an `export` wrapper (gates
    /// namespace-qualified visibility, except inside ambient namespaces).
    pub exported: bool,
}

/// One `namespace`/`module` block's declaration facts, keyed to its symbol.
///
/// `symbol`/`scope` link exactly like [`DeclFact`]: the per-file index of
/// the [`SymbolFact`] for the block name (matched on name + binding start)
/// plus that symbol's owning scope. `namespace A.B { }` parses as nested
/// declarations, so each level carries its own fact. `declare global { }`
/// and `declare module "x" { }` carry no fact (different nodes); their inner
/// declarations are still visited normally.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamespaceFact {
    /// Per-file symbol index of the block name binding.
    pub symbol: u32,
    /// Owning scope (per-file scope index) of [`NamespaceFact::symbol`].
    pub scope: u32,
    /// Block name as written.
    pub name: String,
    /// Span of the whole declaration.
    pub span: Span,
    /// Per-file scope index of the `TsModuleBlock` scope holding the
    /// block's members (`u32::MAX` when indeterminable, e.g. empty blocks).
    /// Qualified `NS.Member` annotations resolve `Member` from this scope
    /// through the binder.
    pub body_scope: u32,
    /// `true` for `declare namespace` (ambient): every member is visible
    /// through qualification, exported or not (probed tsc 7.0.2).
    pub declared: bool,
    /// Whether the declaration sat under an `export` wrapper (gates
    /// qualification of nested namespaces).
    pub exported: bool,
    /// Names directly exported from this block (`export const X`,
    /// `export enum E`, …, but not `export { X }` lists): the solver tells
    /// hidden members (`TS2694`) apart from exported non-types (declined —
    /// kind is unknowable without value facts). In visit order.
    pub exported_members: Vec<String>,
}

/// Everything Pith owns after a frontend pass. Arenas are dropped on return.
#[derive(Clone, Debug)]
pub struct ParsedFile {
    pub file: FileId,
    pub scopes: Vec<ScopeFact>,
    pub symbols: Vec<SymbolFact>,
    pub unresolved: Vec<UnresolvedFact>,
    pub imports: Vec<ImportFact>,
    /// One fact per `const` declarator (identifier bindings only), in
    /// source order. Empty when the file declares no consts.
    pub decls: Vec<DeclFact>,
    /// One fact per named `function` declaration, in source (visitor) order.
    /// Empty when the file declares no functions.
    pub functions: Vec<FunctionFact>,
    /// One fact per direct `f(...)` call expression, in visitor (pre-order)
    /// order. Empty when the file makes no direct calls.
    pub calls: Vec<CallFact>,
    /// One fact per top-level simple `typeof` guard, in visitor (pre-order)
    /// order. Empty when the file has no narrowable guards.
    pub guards: Vec<TypeofGuardFact>,
    /// One decline region per out-of-subset guard/function shape, in visitor
    /// (pre-order) order. Empty when every guard is simple.
    pub decline_regions: Vec<DeclineRegionFact>,
    /// One fact per `interface` declaration, in visitor (pre-order) order.
    /// Empty when the file declares no interfaces.
    pub interfaces: Vec<InterfaceFact>,
    /// One fact per `enum` declaration, in visitor (pre-order) order.
    /// Empty when the file declares no enums.
    pub enums: Vec<EnumFact>,
    /// One fact per `namespace`/`module` block, in visitor (pre-order)
    /// order. Empty when the file declares no namespaces.
    pub namespaces: Vec<NamespaceFact>,
    /// Parser + semantic diagnostics as plain strings (codes deferred to P008).
    pub errors: Vec<String>,
}

// Gap (P005, narrowed by P010): declaration facts (`decls`) are now present;
// per-reference spans still need AstNodes — v1 records counts + names.
// Freshness-relevant occurrence identity will key off NodeId in P005/P006.

// Byte slice of `source` at an Oxc span, or `None` when out of bounds
// (defensive only: spans the parser hands us always slice cleanly).
fn slice_at(source: &str, span: oxc_span::Span) -> Option<&str> {
    let lo = usize::try_from(span.start).ok()?;
    let hi = usize::try_from(span.end).ok()?;
    source.get(lo..hi)
}

/// Targeted declarator collector: a syntactic [`Visit`] pass, so no
/// `AstNodes` store is built (see the module-level build-mode note). All
/// facts are Pith-owned; nothing borrowed escapes the pass.
#[derive(Debug)]
struct DeclCollector<'a> {
    file: FileId,
    source: &'a str,
    /// `(binding name, binding start)` -> per-file symbol index. Keyed on
    /// the start (not the full span) so ESTree-style annotation-extended
    /// ranges can never mis-key; `(name, start)` is injective — one token,
    /// one binding.
    symbols: std::collections::HashMap<(String, u32), u32>,
    /// Per-file symbol index -> owning scope (mirrors `SymbolFact.scope`;
    /// carried so each [`DeclFact`] records its declarator scope directly).
    scopes: std::collections::HashMap<u32, u32>,
    decls: Vec<DeclFact>,
    functions: Vec<FunctionFact>,
    calls: Vec<CallFact>,
    guards: Vec<TypeofGuardFact>,
    declines: Vec<DeclineRegionFact>,
    interfaces: Vec<InterfaceFact>,
    enums: Vec<EnumFact>,
    namespaces: Vec<NamespaceFact>,
    /// `if` statements enclosing the current visit point: anything above zero
    /// means a nested guard (decline, never refine).
    if_depth: u32,
    /// Functions enclosing the current visit point: anything above zero
    /// means a nested closure (its whole body declines — narrowing does not
    /// cross closures, probed tsc 7.0.2).
    fn_depth: u32,
    /// `export <declaration>` wrappers enclosing the current visit point:
    /// anything above zero means the declaration is exported (gates
    /// namespace-qualified visibility solver-side). Specifier lists
    /// (`export { E }`) are not wrappers and do not count (documented limit).
    export_depth: u32,
    /// Innermost-enclosing namespace facts, as indices into `namespaces`:
    /// exported declarations attribute their names to the stack top (see
    /// [`NamespaceFact::exported_members`]).
    ns_stack: Vec<u32>,
}

/// Builds the colon-stripped annotation fact for a `TSTypeAnnotation` span
/// (`: number` -> `"number"`), or `None` when the span does not slice (only
/// possible with recovery from parse errors).
fn annotation_fact(source: &str, file: FileId, span: oxc_span::Span) -> Option<AnnotationFact> {
    let raw = slice_at(source, span)?;
    Some(AnnotationFact {
        text: raw.trim_start_matches(':').trim().to_owned(),
        span: Span {
            file,
            lo: span.start,
            hi: span.end,
        },
    })
}

/// Builds the colon-stripped annotation text for one parameter annotation
/// (`: number` -> `Some("number")`), or `None` when unannotated (or the span
/// does not slice, only possible with recovery from parse errors).
fn param_annotation_text(
    source: &str,
    file: FileId,
    annotation: Option<&TSTypeAnnotation<'_>>,
) -> Option<String> {
    annotation
        .and_then(|ann| annotation_fact(source, file, ann.span))
        .map(|fact| fact.text)
}

/// Collects one function's declared type-parameter names in source order.
///
/// Only plain names feed the solver: any parameter with a constraint
/// (`<T extends string>`), a default (`<T = number>`), or an `in`/`out`/
/// `const` modifier sets the complexity flag (the solver declines those
/// instead of instantiating them). Names still record — the flag, never a
/// miscount, drives the decline. An unsliceable name (only possible with
/// recovery from parse errors) sets the flag and records nothing rather
/// than inventing a key.
fn type_param_facts(source: &str, func: &Function<'_>) -> (Vec<TypeParamFact>, bool) {
    let Some(declared) = func.type_parameters.as_deref() else {
        return (Vec::new(), false);
    };
    let mut params = Vec::with_capacity(declared.params.len());
    let mut complex = false;
    for param in &declared.params {
        match slice_at(source, param.name.span) {
            Some(name) => params.push(TypeParamFact {
                name: name.to_owned(),
            }),
            None => complex = true,
        }
        if param.constraint.is_some()
            || param.default.is_some()
            || param.r#in
            || param.out
            || param.r#const
        {
            complex = true;
        }
    }
    (params, complex)
}

/// Names one interface member key: identifier keys verbatim plus a
/// plain-key flag; anything else (computed, private, literal keys) slices
/// the key text (`"<unknown>"` only on skew) and clears the flag so the
/// caller declines instead of mis-keying.
fn interface_key_name(source: &str, key: &PropertyKey<'_>) -> (String, bool) {
    if let PropertyKey::StaticIdentifier(found) = key {
        if let Some(name) = slice_at(source, found.span) {
            return (name.to_owned(), true);
        }
    }
    let fallback = slice_at(source, key.span()).unwrap_or("<unknown>");
    (fallback.to_owned(), false)
}

/// One declined interface member: real span, recorded name, reason.
///
/// Every complex shape funnels here so none is ever silently dropped; the
/// solver quotes `complex_reason` in its per-member decline.
fn declined_member(
    file: FileId,
    span: oxc_span::Span,
    name: String,
    reason: String,
) -> InterfaceMemberFact {
    InterfaceMemberFact {
        name,
        annotation_text: None,
        span: Span {
            file,
            lo: span.start,
            hi: span.end,
        },
        complex_reason: Some(reason),
    }
}

/// Classifies one interface property signature.
///
/// Plain non-optional properties with identifier keys and a sliced
/// annotation stay checkable (`complex_reason: None`); computed or
/// non-identifier keys, optional members, and missing annotations decline
/// with per-member reasons. The annotation text is verbatim — the solver
/// classifies primitives vs unknown names vs union/complex shapes, exactly
/// like object-annotation members.
fn property_member_fact(
    source: &str,
    file: FileId,
    prop: &TSPropertySignature<'_>,
) -> InterfaceMemberFact {
    let span = Span {
        file,
        lo: prop.span.start,
        hi: prop.span.end,
    };
    let (name, plain) = interface_key_name(source, &prop.key);
    let annotation = prop
        .type_annotation
        .as_ref()
        .and_then(|ann| annotation_fact(source, file, ann.span));
    let reason = if !plain {
        Some(format!(
            "computed or non-identifier key '{name}' is outside the subset"
        ))
    } else if prop.optional {
        Some(format!("optional member '{name}' is outside the subset"))
    } else if annotation.is_none() {
        Some(format!(
            "member '{name}' has no type annotation: outside the subset"
        ))
    } else {
        None
    };
    InterfaceMemberFact {
        name,
        annotation_text: annotation.map(|fact| fact.text),
        span,
        complex_reason: reason,
    }
}

/// Classifies one interface member signature into its fact.
///
/// Only [`property_member_fact`] can stay checkable; methods, index
/// signatures, and call/construct signatures always decline. Index members
/// keep their parameter name for the reason; keyless shapes use fixed
/// descriptors as names (documented, never skipped).
fn interface_member_fact(
    source: &str,
    file: FileId,
    member: &TSSignature<'_>,
) -> InterfaceMemberFact {
    match member {
        TSSignature::TSPropertySignature(prop) => property_member_fact(source, file, prop),
        TSSignature::TSMethodSignature(method) => {
            let (name, _) = interface_key_name(source, &method.key);
            let reason = format!("method signature '{name}' is outside the subset");
            declined_member(file, method.span, name, reason)
        }
        TSSignature::TSIndexSignature(index) => {
            let name = index.parameter.name.to_string();
            let reason = format!("index signature '{name}' is outside the subset");
            declined_member(file, index.span, name, reason)
        }
        TSSignature::TSCallSignatureDeclaration(decl) => declined_member(
            file,
            decl.span,
            "call signature".to_owned(),
            "call signature is outside the subset".to_owned(),
        ),
        TSSignature::TSConstructSignatureDeclaration(decl) => declined_member(
            file,
            decl.span,
            "construct signature".to_owned(),
            "construct signature is outside the subset".to_owned(),
        ),
    }
}

/// Names one enum member: identifier and string-literal names verbatim
/// plus a plain-key flag; computed names slice the key text
/// (`"<unknown>"` only on skew) and clear the flag so the caller declines
/// the member instead of mis-keying.
fn enum_member_name(source: &str, id: &TSEnumMemberName<'_>) -> (String, bool) {
    match id {
        TSEnumMemberName::Identifier(found) => (found.name.to_string(), true),
        TSEnumMemberName::String(literal) => (literal.value.as_str().to_owned(), true),
        _ => {
            let fallback = slice_at(source, id.span()).unwrap_or("<unknown>");
            (fallback.to_owned(), false)
        }
    }
}

/// Auto-increment base threading through one enum's members.
///
/// The first member defaults to `0`; later missing initializers add one to
/// the last numeric value; after a string or computed member there is no
/// base (tsc itself rejects such members without initializers).
#[derive(Clone, Copy)]
enum IncrementBase {
    /// No member seen yet: a missing initializer means `0`.
    First,
    /// Last member was numeric: a missing initializer means `base + 1`.
    Numeric(f64),
    /// Last member was string or computed: a missing initializer declines.
    NonNumeric,
}

/// Classifies one enum member initializer into its value, threading the
/// auto-increment base.
///
/// Returns the value plus the base for the next member. Numeric and string
/// literals record values; everything else (identifiers, unary/binary
/// expressions, member accesses, …) is computed with a reason, as is a
/// missing initializer with no numeric base.
fn enum_member_value(
    initializer: Option<&Expression<'_>>,
    base: IncrementBase,
) -> (EnumValueKind, IncrementBase) {
    let Some(expression) = initializer else {
        return match base {
            IncrementBase::First => (EnumValueKind::Number(0.0), IncrementBase::Numeric(0.0)),
            IncrementBase::Numeric(found) => (
                EnumValueKind::Number(found + 1.0),
                IncrementBase::Numeric(found + 1.0),
            ),
            IncrementBase::NonNumeric => (
                EnumValueKind::Computed {
                    reason: "auto-increment after a non-numeric member is outside the subset"
                        .to_owned(),
                },
                IncrementBase::NonNumeric,
            ),
        };
    };
    match expression {
        Expression::NumericLiteral(literal) => (
            EnumValueKind::Number(literal.value),
            IncrementBase::Numeric(literal.value),
        ),
        Expression::StringLiteral(literal) => (
            EnumValueKind::String(literal.value.as_str().to_owned()),
            IncrementBase::NonNumeric,
        ),
        _ => (
            EnumValueKind::Computed {
                reason: "non-literal initializer is outside the subset".to_owned(),
            },
            IncrementBase::NonNumeric,
        ),
    }
}

/// Whether `inner` lies fully inside `outer` (same file, closed bounds).
fn span_contains(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.lo <= inner.lo && inner.hi <= outer.hi
}

/// Fills `body_scope` on each namespace fact: the child of the owning scope
/// holding span-contained member symbols (see the module-level namespace
/// note). Scopes arrive root-first, so the first match wins deterministically;
/// facts whose owning scope missed stay `u32::MAX` (empty blocks).
fn assign_namespace_body_scopes(
    scopes: &[ScopeFact],
    symbols: &[SymbolFact],
    namespaces: &mut [NamespaceFact],
) {
    for namespace in namespaces.iter_mut() {
        if namespace.scope == u32::MAX {
            continue;
        }
        for scope in scopes {
            if scope.parent != namespace.scope {
                continue;
            }
            let owned = symbols.iter().any(|symbol| {
                symbol.scope == scope.index && span_contains(namespace.span, symbol.span)
            });
            if owned {
                namespace.body_scope = scope.index;
                break;
            }
        }
    }
}

/// Nearest same-name symbol at or before `start`: the overload-merge owner.
///
/// Oxc folds overload signatures into the first declaration's symbol, whose
/// span precedes every merged overload. Callers try the exact
/// `(name, start)` key first: shadowing never reaches here (each shadow has
/// its own exact-span symbol), so a hit here is a merged redeclaration.
/// Returns `None` when no same-name symbol precedes — then the caller skips
/// rather than inventing.
fn nearest_preceding_symbol(
    symbols: &std::collections::HashMap<(String, u32), u32>,
    name: &str,
    start: u32,
) -> Option<u32> {
    symbols
        .iter()
        .filter(|((candidate, _), _)| candidate.as_str() == name)
        .filter_map(|((_, candidate_start), index)| {
            (*candidate_start <= start).then_some((*candidate_start, *index))
        })
        .max_by_key(|(candidate_start, _)| *candidate_start)
        .map(|(_, index)| index)
}

/// Classifies one returned/member value expression into its literal kind.
///
/// Only plain literals classify; identifiers other than `undefined`,
/// parenthesized expressions, and every other shape are [`ReturnKind::NonLiteral`]
/// (expression facts the adapter does not emit yet) — exactly like const
/// initializer classification.
fn return_kind(source: &str, expression: &Expression<'_>) -> ReturnKind {
    match expression {
        Expression::NumericLiteral(_) => ReturnKind::Number,
        Expression::StringLiteral(_) => ReturnKind::String,
        Expression::BooleanLiteral(literal) => ReturnKind::Boolean(literal.value),
        Expression::NullLiteral(_) => ReturnKind::Null,
        Expression::Identifier(ident) => {
            if slice_at(source, ident.span).is_some_and(|text| text == "undefined") {
                ReturnKind::Undefined
            } else {
                ReturnKind::NonLiteral
            }
        }
        _ => ReturnKind::NonLiteral,
    }
}

/// Classifies one call argument into its literal kind.
///
/// A thin exhaustive map over [`return_kind`] (no duplicated match arms):
/// the boolean payload is dropped because `TS2345` messages spell widened
/// names only (probed 7.0.2) — exactly like const initializer classification.
fn call_arg_kind(source: &str, expression: &Expression<'_>) -> CallArgKind {
    match return_kind(source, expression) {
        ReturnKind::Number => CallArgKind::Number,
        ReturnKind::String => CallArgKind::String,
        ReturnKind::Boolean(_) => CallArgKind::Boolean,
        ReturnKind::Null => CallArgKind::Null,
        ReturnKind::Undefined => CallArgKind::Undefined,
        ReturnKind::NonLiteral => CallArgKind::NonLiteral,
    }
}

/// Classifies a returned `{ ... }` literal into member facts (literal
/// order), or `None` when a member is unrepresentable (spread, method,
/// accessor, computed or non-identifier key): the caller marks the body
/// [`FunctionBodyFact::Complex`] instead of mis-keying.
fn return_members(
    source: &str,
    file: FileId,
    properties: &[ObjectPropertyKind<'_>],
) -> Option<Vec<ReturnMemberFact>> {
    let mut members = Vec::with_capacity(properties.len());
    for property in properties {
        let ObjectPropertyKind::ObjectProperty(member) = property else {
            return None;
        };
        if member.method || member.computed || member.kind != PropertyKind::Init {
            return None;
        }
        let PropertyKey::StaticIdentifier(key) = &member.key else {
            return None;
        };
        let name = slice_at(source, key.span)?;
        let span = member.value.span();
        members.push(ReturnMemberFact {
            name: name.to_owned(),
            kind: return_kind(source, &member.value),
            span: Span {
                file,
                lo: span.start,
                hi: span.end,
            },
        });
    }
    Some(members)
}

/// Classifies one function body into its [`FunctionBodyFact`].
///
/// `declared` is the `declare` modifier off the `Function` node (ambient
/// declarations never carry a body node); it only surfaces on
/// [`FunctionBodyFact::NoBody`].
fn function_body_fact(
    source: &str,
    file: FileId,
    body: Option<&FunctionBody<'_>>,
    declared: bool,
) -> FunctionBodyFact {
    let Some(body) = body else {
        return FunctionBodyFact::NoBody { declared };
    };
    if body.statements.is_empty() {
        return FunctionBodyFact::Empty;
    }
    if body.statements.len() != 1 {
        return FunctionBodyFact::Complex;
    }
    let Statement::ReturnStatement(ret) = &body.statements[0] else {
        return FunctionBodyFact::Complex;
    };
    let Some(argument) = ret.argument.as_ref() else {
        // Bare `return;`: no literal kind to record.
        return FunctionBodyFact::Complex;
    };
    let span = argument.span();
    let span = Span {
        file,
        lo: span.start,
        hi: span.end,
    };
    if let Expression::ObjectExpression(object) = argument {
        let Some(members) = return_members(source, file, &object.properties) else {
            return FunctionBodyFact::Complex;
        };
        FunctionBodyFact::SingleReturn(SingleReturnFact {
            kind: ReturnKind::NonLiteral,
            span,
            members: Some(members),
        })
    } else {
        FunctionBodyFact::SingleReturn(SingleReturnFact {
            kind: return_kind(source, argument),
            span,
            members: None,
        })
    }
}

/// Pushes one narrowing decline region onto the collector.
fn decline_region(collector: &mut DeclCollector<'_>, span: Span, reason: &str) {
    collector.declines.push(DeclineRegionFact {
        span,
        reason: reason.to_owned(),
    });
}

/// The `typeof <ident>` side of a simple guard comparison: name plus span.
#[must_use]
fn typeof_operand(file: FileId, operand: &Expression<'_>) -> Option<(String, Span)> {
    let Expression::UnaryExpression(unary) = operand else {
        return None;
    };
    if unary.operator != UnaryOperator::Typeof {
        return None;
    }
    let Expression::Identifier(ident) = &unary.argument else {
        return None;
    };
    Some((
        ident.name.to_string(),
        Span {
            file,
            lo: ident.span.start,
            hi: ident.span.end,
        },
    ))
}

/// The `"<lit>"` side of a simple guard comparison: literal text.
#[must_use]
fn string_operand(operand: &Expression<'_>) -> Option<String> {
    let Expression::StringLiteral(literal) = operand else {
        return None;
    };
    Some(literal.value.as_str().to_owned())
}

/// Classifies one `if` test as a simple typeof guard: `typeof x === "<lit>"`
/// or `!==` in either operand order, transparent through one layer of
/// parentheses around the whole condition. Returns target name/span, matched
/// text, and negation. Anything else is `None` (the caller declines).
#[must_use]
fn classify_typeof_test(
    file: FileId,
    mut test: &Expression<'_>,
) -> Option<(String, Span, String, bool)> {
    if let Expression::ParenthesizedExpression(parenthesized) = test {
        test = &parenthesized.expression;
    }
    let Expression::BinaryExpression(binary) = test else {
        return None;
    };
    let negated = match binary.operator {
        BinaryOperator::StrictEquality => false,
        BinaryOperator::StrictInequality => true,
        _ => return None,
    };
    if let (Some((target, target_span)), Some(matched)) = (
        typeof_operand(file, &binary.left),
        string_operand(&binary.right),
    ) {
        return Some((target, target_span, matched, negated));
    }
    if let (Some((target, target_span)), Some(matched)) = (
        typeof_operand(file, &binary.right),
        string_operand(&binary.left),
    ) {
        return Some((target, target_span, matched, negated));
    }
    None
}

/// Whether a branch diverges: bare/valued `return` or `throw`, directly or as
/// the only statement of a block. Only these shapes mark a guard
/// early-return (probed tsc 7.0.2: each refines the code after the `if`).
#[must_use]
fn is_divergent(statement: &Statement<'_>) -> bool {
    match statement {
        Statement::ReturnStatement(_) | Statement::ThrowStatement(_) => true,
        Statement::BlockStatement(block) => block.body.len() == 1 && is_divergent(&block.body[0]),
        _ => false,
    }
}

impl DeclCollector<'_> {
    /// Attributes `name` to the innermost enclosing namespace when declared
    /// under an `export` wrapper (see [`NamespaceFact::exported_members`]).
    /// Top-level declarations have no stack top and record nothing: their
    /// own `exported` flags (read at record time) are what tail resolution
    /// never consults.
    fn note_exported(&mut self, name: &str) {
        if self.export_depth == 0 {
            return;
        }
        if let Some(&top) = self.ns_stack.last() {
            if let Some(fact) = self
                .namespaces
                .get_mut(usize::try_from(top).unwrap_or(usize::MAX))
            {
                fact.exported_members.push(name.to_owned());
            }
        }
    }

    /// Attributes one variable declarator's name when it is a plain
    /// identifier binding (destructured patterns bind many symbols and are
    /// skipped, mirroring [`record_declarator`]).
    fn note_declarator(&mut self, declarator: &VariableDeclarator<'_>) {
        let BindingPattern::BindingIdentifier(binding) = &declarator.id else {
            return;
        };
        if let Some(name) = slice_at(self.source, binding.span) {
            self.note_exported(name);
        }
    }

    /// Records one declarator when it is a `const` identifier binding.
    /// Destructured patterns bind many symbols and are skipped.
    fn record_declarator(&mut self, declarator: &VariableDeclarator<'_>) {
        let BindingPattern::BindingIdentifier(binding) = &declarator.id else {
            return;
        };
        let name = slice_at(self.source, binding.span);
        let Some(name) = name else { return };
        self.note_exported(name);
        let Some(&symbol) = self.symbols.get(&(name.to_owned(), binding.span.start)) else {
            // No matching symbol (only possible with recovery from parse
            // errors): skip rather than invent a key.
            return;
        };

        let annotation = declarator
            .type_annotation
            .as_ref()
            .and_then(|ann| annotation_fact(self.source, self.file, ann.span));

        let init = declarator.init.as_ref().map(|expression| {
            let span = expression.span();
            let kind = match expression {
                Expression::NumericLiteral(_) => InitKind::Number,
                Expression::StringLiteral(_) => InitKind::String,
                Expression::BooleanLiteral(_) => InitKind::Boolean,
                Expression::NullLiteral(_) => InitKind::Null,
                Expression::Identifier(ident) => {
                    if slice_at(self.source, ident.span).is_some_and(|text| text == "undefined") {
                        InitKind::Undefined
                    } else {
                        InitKind::NonLiteral
                    }
                }
                _ => InitKind::NonLiteral,
            };
            InitFact {
                kind,
                span: Span {
                    file: self.file,
                    lo: span.start,
                    hi: span.end,
                },
            }
        });

        self.decls.push(DeclFact {
            symbol,
            scope: self.scopes.get(&symbol).copied().unwrap_or(u32::MAX),
            annotation,
            init,
        });
    }

    /// Records one function when it is a named function declaration.
    ///
    /// Function expressions, arrows, and methods never reach a fact (the
    /// `FunctionType` gate); anonymous default exports have no binding to
    /// key on. Identifier parameters record name + annotated-ness; any
    /// other pattern (including a non-identifier rest element) sets
    /// `params_complex` and stops the list rather than mis-keying.
    fn record_function(&mut self, func: &Function<'_>) {
        if !matches!(
            func.r#type,
            FunctionType::FunctionDeclaration | FunctionType::TSDeclareFunction
        ) {
            return;
        }
        let Some(id) = func.id.as_ref() else {
            return;
        };
        let name = slice_at(self.source, id.span);
        let Some(name) = name else { return };
        self.note_exported(name);
        let Some(symbol) = self
            .symbols
            .get(&(name.to_owned(), id.span.start))
            .copied()
            .or_else(|| nearest_preceding_symbol(&self.symbols, name, id.span.start))
        else {
            // No matching symbol (only possible with recovery from parse
            // errors): skip rather than invent a key.
            return;
        };

        let mut params = Vec::new();
        let mut params_complex = false;
        for item in &func.params.items {
            let BindingPattern::BindingIdentifier(binding) = &item.pattern else {
                params_complex = true;
                break;
            };
            let Some(param) = slice_at(self.source, binding.span) else {
                params_complex = true;
                break;
            };
            params.push(FunctionParamFact {
                name: param.to_owned(),
                annotated: item.type_annotation.is_some(),
                annotation_text: param_annotation_text(
                    self.source,
                    self.file,
                    item.type_annotation.as_deref(),
                ),
                // A defaulted `b: T = …` widens arity to a range exactly
                // like `b?: T`, so both mark `optional` for the call checker.
                optional: item.optional || item.initializer.is_some(),
                is_rest: false,
            });
        }
        if !params_complex {
            if let Some(rest) = func.params.rest.as_ref() {
                match &rest.rest.argument {
                    BindingPattern::BindingIdentifier(binding) => {
                        match slice_at(self.source, binding.span) {
                            Some(param) => params.push(FunctionParamFact {
                                name: param.to_owned(),
                                annotated: rest.type_annotation.is_some(),
                                annotation_text: param_annotation_text(
                                    self.source,
                                    self.file,
                                    rest.type_annotation.as_deref(),
                                ),
                                optional: false,
                                is_rest: true,
                            }),
                            None => {
                                params_complex = true;
                            }
                        }
                    }
                    _ => {
                        params_complex = true;
                    }
                }
            }
        }

        let return_annotation = func
            .return_type
            .as_ref()
            .and_then(|ann| annotation_fact(self.source, self.file, ann.span));
        let body = function_body_fact(self.source, self.file, func.body.as_deref(), func.declare);
        let (type_params, type_params_complex) = type_param_facts(self.source, func);
        self.functions.push(FunctionFact {
            symbol,
            scope: self.scopes.get(&symbol).copied().unwrap_or(u32::MAX),
            params,
            params_complex,
            type_params,
            type_params_complex,
            return_annotation,
            body,
        });
    }

    /// Records one interface declaration with its member facts.
    ///
    /// Symbol linkage reuses the `(name, binding start)` keying of
    /// [`DeclFact`]: merged pairs (`interface Foo` plus `const Foo`) share
    /// oxc's pre-merged symbol, so the interface fact links it while the
    /// const finds no exact key (see the module-level merge note).
    /// Anonymous default-exported interfaces have no sliceable name and are
    /// skipped. Heritage names slice off the parent type spans; an
    /// unsliceable name (only possible with recovery from parse errors)
    /// records `""` rather than dropping the clause.
    fn record_interface(&mut self, decl: &TSInterfaceDeclaration<'_>) {
        let Some(name) = slice_at(self.source, decl.id.span) else {
            return;
        };
        self.note_exported(name);
        let Some(&symbol) = self.symbols.get(&(name.to_owned(), decl.id.span.start)) else {
            // No matching symbol (only possible with recovery from parse
            // errors): skip rather than invent a key.
            return;
        };
        let source = self.source;
        let file = self.file;
        let heritage = decl
            .extends
            .iter()
            .map(|parent| {
                let span = parent.span;
                InterfaceHeritageFact {
                    name: slice_at(source, parent.type_name.span())
                        .unwrap_or("")
                        .to_owned(),
                    span: Span {
                        file,
                        lo: span.start,
                        hi: span.end,
                    },
                }
            })
            .collect();
        let members = decl
            .body
            .body
            .iter()
            .map(|member| interface_member_fact(source, file, member))
            .collect();
        let span = decl.span;
        let exported = self.export_depth > 0;
        self.interfaces.push(InterfaceFact {
            symbol,
            scope: self.scopes.get(&symbol).copied().unwrap_or(u32::MAX),
            name: name.to_owned(),
            span: Span {
                file,
                lo: span.start,
                hi: span.end,
            },
            members,
            heritage,
            has_type_params: decl.type_parameters.is_some(),
            exported,
        });
    }

    /// Records one enum declaration with its member facts.
    ///
    /// Symbol linkage reuses the `(name, binding start)` keying of
    /// [`DeclFact`]; anonymous enums cannot occur. Member values thread the
    /// auto-increment base in source order (see [`enum_member_value`]);
    /// computed names decline their member. `exported` reads the enclosing
    /// `export`-wrapper depth; `body_scope` is filled post-pass.
    fn record_enum(&mut self, decl: &TSEnumDeclaration<'_>) {
        let Some(name) = slice_at(self.source, decl.id.span) else {
            return;
        };
        self.note_exported(name);
        let Some(&symbol) = self.symbols.get(&(name.to_owned(), decl.id.span.start)) else {
            // No matching symbol (only possible with recovery from parse
            // errors): skip rather than invent a key.
            return;
        };
        let source = self.source;
        let file = self.file;
        let mut base = IncrementBase::First;
        let members = decl
            .body
            .members
            .iter()
            .map(|member| {
                let span = Span {
                    file,
                    lo: member.span.start,
                    hi: member.span.end,
                };
                let (member_name, plain) = enum_member_name(source, &member.id);
                if !plain {
                    base = IncrementBase::NonNumeric;
                    return EnumMemberFact {
                        name: member_name,
                        value: EnumValueKind::Computed {
                            reason: "computed member name is outside the subset".to_owned(),
                        },
                        span,
                    };
                }
                let (value, next) = enum_member_value(member.initializer.as_ref(), base);
                base = next;
                EnumMemberFact {
                    name: member_name,
                    value,
                    span,
                }
            })
            .collect();
        let span = decl.span;
        self.enums.push(EnumFact {
            symbol,
            scope: self.scopes.get(&symbol).copied().unwrap_or(u32::MAX),
            name: name.to_owned(),
            span: Span {
                file,
                lo: span.start,
                hi: span.end,
            },
            members,
            is_const: decl.r#const,
            declared: decl.declare,
            exported: self.export_depth > 0,
        });
    }

    /// Records one namespace/module block.
    ///
    /// Symbol linkage reuses the `(name, binding start)` keying of
    /// [`DeclFact`]. Nested `namespace A.B { }` declarations record one fact
    /// per level (the walk visits each); `exported` reads the enclosing
    /// `export`-wrapper depth; `body_scope` is filled post-pass (see
    /// [`assign_namespace_body_scopes`]).
    fn record_namespace(&mut self, decl: &TSNamespaceDeclaration<'_>) {
        let Some(name) = slice_at(self.source, decl.id.span) else {
            return;
        };
        self.note_exported(name);
        let Some(&symbol) = self.symbols.get(&(name.to_owned(), decl.id.span.start)) else {
            // No matching symbol (only possible with recovery from parse
            // errors): skip rather than invent a key.
            return;
        };
        let span = decl.span;
        self.namespaces.push(NamespaceFact {
            symbol,
            scope: self.scopes.get(&symbol).copied().unwrap_or(u32::MAX),
            name: name.to_owned(),
            span: Span {
                file: self.file,
                lo: span.start,
                hi: span.end,
            },
            body_scope: u32::MAX,
            declared: decl.declare,
            exported: self.export_depth > 0,
            exported_members: Vec::new(),
        });
    }

    /// Records one call expression when it is a direct `f(...)` call.
    ///
    /// Anything else emits no fact, never a wrong one: member/computed calls
    /// (`obj.m()`), `super(...)`, and every other non-identifier callee fail
    /// the `Identifier` match; optional chains (`f?.()`) hit the `optional`
    /// gate (tsc checks their arity, but the shape is outside the subset);
    /// any spread element (`f(...xs)`) drops the whole call (arity is
    /// unknowable from facts). Unclassifiable arguments still occupy their
    /// position as [`CallArgKind::NonLiteral`] so arity checks keep working.
    fn record_call(&mut self, call: &CallExpression<'_>) {
        if call.optional {
            return;
        }
        let Expression::Identifier(ident) = &call.callee else {
            return;
        };
        if call.arguments.iter().any(Argument::is_spread) {
            return;
        }
        let mut args = Vec::with_capacity(call.arguments.len());
        for argument in &call.arguments {
            // Only `SpreadElement` converts to `None`, already excluded
            // above: this skips rather than mis-records on skew.
            let Some(expression) = argument.as_expression() else {
                return;
            };
            let span = expression.span();
            args.push(CallArgFact {
                kind: call_arg_kind(self.source, expression),
                span: Span {
                    file: self.file,
                    lo: span.start,
                    hi: span.end,
                },
            });
        }
        let callee_span = Span {
            file: self.file,
            lo: ident.span.start,
            hi: ident.span.end,
        };
        self.calls.push(CallFact {
            callee: ident.name.to_string(),
            callee_span,
            span: Span {
                file: self.file,
                lo: call.span.start,
                hi: call.span.end,
            },
            args,
        });
    }

    /// Records one `if` statement: a [`TypeofGuardFact`] for top-level simple
    /// typeof guards, otherwise a [`DeclineRegionFact`] over the whole
    /// statement (never a wrong guard fact).
    fn record_if(&mut self, it: &IfStatement<'_>) {
        let file = self.file;
        let if_span = Span {
            file,
            lo: it.span.start,
            hi: it.span.end,
        };
        if self.if_depth > 0 {
            decline_region(
                self,
                if_span,
                "nested guard: narrowing inside another guard is outside the subset",
            );
            return;
        }
        let Some((target, target_span, matched, negated)) = classify_typeof_test(file, &it.test)
        else {
            decline_region(
                self,
                if_span,
                "guard condition is not a simple typeof comparison: outside the subset",
            );
            return;
        };
        if matches!(&it.alternate, Some(Statement::IfStatement(_))) {
            decline_region(
                self,
                if_span,
                "else-if chain: narrowing across else-if is outside the subset",
            );
            return;
        }
        let then_span = it.consequent.span();
        let else_span = it.alternate.as_ref().map(GetSpan::span);
        let early_return = it.alternate.is_none() && is_divergent(&it.consequent);
        self.guards.push(TypeofGuardFact {
            target,
            target_span,
            matched,
            negated,
            then_span: Span {
                file,
                lo: then_span.start,
                hi: then_span.end,
            },
            else_span: else_span.map(|span| Span {
                file,
                lo: span.start,
                hi: span.end,
            }),
            early_return,
            if_span,
        });
    }
}

impl<'a> Visit<'a> for DeclCollector<'a> {
    fn visit_variable_declaration(&mut self, it: &VariableDeclaration<'a>) {
        if matches!(it.kind, VariableDeclarationKind::Const) {
            for declarator in &it.declarations {
                self.record_declarator(declarator);
            }
        } else if self.export_depth > 0 {
            // `let`/`var` emit no decl facts (P010 gap), but their exported
            // names still count for namespace visibility.
            for declarator in &it.declarations {
                self.note_declarator(declarator);
            }
        }
        // Keep walking: initializers may nest functions/blocks that declare
        // their own consts (`const f = () => { const y = 1; … }`).
        walk::walk_variable_declaration(self, it);
    }

    fn visit_function(&mut self, it: &Function<'a>, flags: ScopeFlags) {
        self.record_function(it);
        if self.fn_depth > 0 {
            decline_region(
                self,
                Span {
                    file: self.file,
                    lo: it.span.start,
                    hi: it.span.end,
                },
                "nested function boundary: narrowing does not cross closures",
            );
        }
        // Keep walking: bodies nest consts and further function declarations
        // (`function o() { const y = 1; function i() { return y; } … }`).
        self.fn_depth = self.fn_depth.saturating_add(1);
        walk::walk_function(self, it, flags);
        self.fn_depth = self.fn_depth.saturating_sub(1);
    }

    fn visit_arrow_function_expression(&mut self, it: &ArrowFunctionExpression<'a>) {
        if self.fn_depth > 0 {
            decline_region(
                self,
                Span {
                    file: self.file,
                    lo: it.span.start,
                    hi: it.span.end,
                },
                "nested function boundary: narrowing does not cross closures",
            );
        }
        self.fn_depth = self.fn_depth.saturating_add(1);
        walk::walk_arrow_function_expression(self, it);
        self.fn_depth = self.fn_depth.saturating_sub(1);
    }

    fn visit_ts_interface_declaration(&mut self, it: &TSInterfaceDeclaration<'a>) {
        self.record_interface(it);
        // Keep walking: member types nest no declarators, but the walk keeps
        // the visitor total over future AST shapes (mirrors the other
        // record-then-walk methods).
        walk::walk_ts_interface_declaration(self, it);
    }

    fn visit_ts_enum_declaration(&mut self, it: &TSEnumDeclaration<'a>) {
        self.record_enum(it);
        // Keep walking: initializers may nest functions/blocks that declare
        // their own consts (`enum E { A = (() => 1)() }`).
        walk::walk_ts_enum_declaration(self, it);
    }

    fn visit_ts_namespace_declaration(&mut self, it: &TSNamespaceDeclaration<'a>) {
        // Keep walking: members nest consts, functions, interfaces, enums,
        // and further namespaces, each gaining real scopes/symbols/facts.
        // Nested `namespace A.B { }` visits once per level. The stack
        // attributes exported members to the innermost block; a skipped
        // record (only possible with recovery from parse errors) pushes
        // nothing, so members attribute outward rather than mis-attributing.
        let before = self.namespaces.len();
        self.record_namespace(it);
        let pushed = self.namespaces.len() > before;
        if pushed {
            let top = u32::try_from(before).unwrap_or(u32::MAX);
            self.ns_stack.push(top);
        }
        walk::walk_ts_namespace_declaration(self, it);
        if pushed {
            self.ns_stack.pop();
        }
    }

    fn visit_export_declaration(&mut self, it: &ExportDeclaration<'a>) {
        // `export <declaration>` wrappers mark exportedness (gates
        // namespace-qualified visibility solver-side).
        self.export_depth = self.export_depth.saturating_add(1);
        walk::walk_export_declaration(self, it);
        self.export_depth = self.export_depth.saturating_sub(1);
    }

    fn visit_export_default_declaration(&mut self, it: &ExportDefaultDeclaration<'a>) {
        self.export_depth = self.export_depth.saturating_add(1);
        walk::walk_export_default_declaration(self, it);
        self.export_depth = self.export_depth.saturating_sub(1);
    }

    fn visit_class(&mut self, it: &Class<'a>) {
        // Named classes count for namespace visibility (their qualified
        // uses decline as non-types solver-side); anonymous class
        // expressions carry no member name. The scope-membership guard
        // keeps expression-local names from ever matching.
        if let Some(id) = it.id.as_ref() {
            if let Some(name) = slice_at(self.source, id.span) {
                self.note_exported(name);
            }
        }
        // Keep walking: static blocks and computed keys nest declarators.
        walk::walk_class(self, it);
    }

    fn visit_ts_type_alias_declaration(&mut self, it: &TSTypeAliasDeclaration<'a>) {
        // Type aliases count for namespace visibility (their qualified uses
        // decline as non-types solver-side — kind is unknowable facts-side).
        if let Some(name) = slice_at(self.source, it.id.span) {
            self.note_exported(name);
        }
        // Keep walking: the aliased type nests no declarators, but the walk
        // keeps the visitor total over future AST shapes.
        walk::walk_ts_type_alias_declaration(self, it);
    }

    fn visit_if_statement(&mut self, it: &IfStatement<'a>) {
        self.record_if(it);
        // Keep walking: branches nest consts and further guards (which
        // decline as nested) alongside calls and declarations. Note a direct
        // `else if` alternate visits at depth+1 like any nested `if`, so a
        // chain carries both its whole-chain decline and one nested decline
        // for the inner link: doubly covered, never reasoned about.
        self.if_depth = self.if_depth.saturating_add(1);
        walk::walk_if_statement(self, it);
        self.if_depth = self.if_depth.saturating_sub(1);
    }

    fn visit_call_expression(&mut self, it: &CallExpression<'a>) {
        self.record_call(it);
        // Keep walking: arguments nest further calls (`f(g(1))` yields a fact
        // per call) and declarations inside them.
        walk::walk_call_expression(self, it);
    }
}

/// Parse TypeScript source into Pith-owned facts.
///
/// `path_hint` (e.g. `"a.ts"`, `"b.tsx"`) selects module/script + JSX; only
/// the suffix behavior crosses the boundary, never Oxc types.
#[must_use]
pub fn parse_module(file: FileId, path_hint: &str, source: &str) -> ParsedFile {
    let allocator = Allocator::default();
    let source_type = SourceType::from_path(path_hint).unwrap_or_default();
    let parse = Parser::new(&allocator, source, source_type).parse();

    let mut errors: Vec<String> = parse.diagnostics.iter().map(|e| format!("{e:?}")).collect();

    let semantic = SemanticBuilder::new().build(&parse.program);
    errors.extend(semantic.diagnostics.iter().map(|e| format!("{e:?}")));
    let scoping = semantic.semantic.scoping();

    let span_of = |s: oxc_span::Span| Span {
        file,
        lo: s.start,
        hi: s.end,
    };

    // Scopes: descendants-from-root is root-first; re-index per file.
    // (The counter must live outside the loop: indexing off `scopes.len()`
    // here would pin every scope to 0, since pushes happen below.)
    let mut scope_index_of = std::collections::HashMap::new();
    let mut next_scope: u32 = 0;
    for scope_id in scoping.scope_descendants_from_root() {
        scope_index_of.insert(scope_id, next_scope);
        next_scope = next_scope.saturating_add(1);
    }
    let mut scopes = Vec::new();
    for scope_id in scoping.scope_descendants_from_root() {
        let index = scope_index_of[&scope_id];
        let parent = scoping
            .scope_parent_id(scope_id)
            .and_then(|p| scope_index_of.get(&p).copied())
            .unwrap_or(u32::MAX);
        scopes.push(ScopeFact {
            index,
            parent,
            flags: u32::from(scoping.scope_flags(scope_id).bits()),
        });
    }

    // Symbols + resolved references. Scope linkage uses the SAME per-file
    // re-indexing as ScopeFact.index (never the raw Oxc ScopeId number).
    let mut symbols = Vec::new();
    for symbol_id in scoping.symbol_ids() {
        let refs = scoping.get_resolved_reference_ids(symbol_id);
        let mut names: Vec<String> = refs
            .iter()
            .filter_map(|r| scoping.get_reference_name(*r).map(str::to_owned))
            .collect();
        names.sort();
        names.dedup();
        let scope = scope_index_of
            .get(&scoping.symbol_scope_id(symbol_id))
            .copied()
            .unwrap_or(u32::MAX);
        symbols.push(SymbolFact {
            index: sat_u32(symbols.len()),
            scope,
            name: scoping.symbol_name(symbol_id).to_owned(),
            span: span_of(scoping.symbol_span(symbol_id)),
            flags: scoping.symbol_flags(symbol_id).bits(),
            resolved_ref_count: sat_u32(refs.len()),
            resolved_ref_names: names,
        });
    }

    // Root unresolved references. Names live in the map KEYS: `Reference`
    // carries no name and `get_reference_name` resolves via symbol (None here).
    let mut unresolved = Vec::new();
    for (name, ids) in scoping.root_unresolved_references() {
        unresolved.push(UnresolvedFact {
            name: name.as_str().to_owned(),
            count: sat_u32(ids.len()),
        });
    }
    unresolved.sort_by(|a, b| a.name.cmp(&b.name));

    // Module record: import specifiers.
    let imports = parse
        .module_record
        .import_entries
        .iter()
        .map(|e| ImportFact {
            specifier: e.module_request.name.to_string(),
            span: span_of(e.module_request.span),
        })
        .collect();

    let collected = collect_decls(file, source, &parse.program, &symbols, &scopes);
    ParsedFile {
        file,
        scopes,
        symbols,
        unresolved,
        imports,
        decls: collected.decls,
        functions: collected.functions,
        calls: collected.calls,
        guards: collected.guards,
        decline_regions: collected.declines,
        interfaces: collected.interfaces,
        enums: collected.enums,
        namespaces: collected.namespaces,
        errors,
    }
}

/// Owned fact collections from one frontend pass, bundled so the collector
/// return stays lean.
struct CollectedFacts {
    decls: Vec<DeclFact>,
    functions: Vec<FunctionFact>,
    calls: Vec<CallFact>,
    guards: Vec<TypeofGuardFact>,
    declines: Vec<DeclineRegionFact>,
    interfaces: Vec<InterfaceFact>,
    enums: Vec<EnumFact>,
    namespaces: Vec<NamespaceFact>,
}

/// Runs the targeted declarator walk and returns owned facts.
///
/// Symbol linkage resolves each declarator's `(name, binding start)` to the
/// per-file [`SymbolFact`] index built above; facts come out in source
/// (visitor) order, so the sequences are deterministic. Namespace
/// `body_scope` values are filled post-pass from `scopes` plus `symbols`.
fn collect_decls<'a>(
    file: FileId,
    source: &'a str,
    program: &Program<'a>,
    symbols: &[SymbolFact],
    scopes: &[ScopeFact],
) -> CollectedFacts {
    let mut index_of = std::collections::HashMap::new();
    let mut scope_of = std::collections::HashMap::new();
    for symbol in symbols {
        let previous = index_of.insert((symbol.name.clone(), symbol.span.lo), symbol.index);
        debug_assert!(
            previous.is_none(),
            "duplicate (name, binding-start) symbol key"
        );
        scope_of.insert(symbol.index, symbol.scope);
    }
    let mut collector = DeclCollector {
        file,
        source,
        symbols: index_of,
        scopes: scope_of,
        decls: Vec::new(),
        functions: Vec::new(),
        calls: Vec::new(),
        guards: Vec::new(),
        declines: Vec::new(),
        interfaces: Vec::new(),
        enums: Vec::new(),
        namespaces: Vec::new(),
        if_depth: 0,
        fn_depth: 0,
        export_depth: 0,
        ns_stack: Vec::new(),
    };
    collector.visit_program(program);
    let DeclCollector {
        decls,
        functions,
        calls,
        guards,
        declines,
        interfaces,
        mut namespaces,
        enums,
        ..
    } = collector;
    assign_namespace_body_scopes(scopes, symbols, &mut namespaces);
    CollectedFacts {
        decls,
        functions,
        calls,
        guards,
        declines,
        interfaces,
        enums,
        namespaces,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
import { b } from "./b";
const x: number = 1;
export function f(a: string): string { return a + b; }
"#;

    #[test]
    fn adapter_extracts_boundary_facts() {
        let pf = parse_module(FileId(0), "a.ts", SAMPLE);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        // root scope + module scope at minimum
        assert!(!pf.scopes.is_empty());
        assert_eq!(pf.scopes[0].parent, u32::MAX);
        let names: Vec<&str> = pf.symbols.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"x"), "symbols: {names:?}");
        assert!(names.contains(&"f"), "symbols: {names:?}");
        // all spans anchored to our file
        assert!(pf.symbols.iter().all(|s| s.span.file == FileId(0)));
        // import specifier captured with span
        assert_eq!(pf.imports.len(), 1);
        assert_eq!(pf.imports[0].specifier, "./b");
        assert_eq!(pf.imports[0].span.file, FileId(0));
    }

    #[test]
    fn unresolved_globals_reported() {
        let pf = parse_module(FileId(1), "g.ts", "console.log(missing);\n");
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        let names: Vec<&str> = pf.unresolved.iter().map(|u| u.name.as_str()).collect();
        assert!(names.contains(&"console"), "unresolved: {names:?}");
        assert!(names.contains(&"missing"), "unresolved: {names:?}");
    }

    #[test]
    fn decl_facts_annotated_literal_exact_spans() {
        // Offsets hand-counted, cross-checked with the oxc parser
        // (`const a: number = 1;`: `a` at 6, `:` at 7, `number` at 9..15,
        // `1` at 18). Annotation span is the colon-inclusive
        // TSTypeAnnotation range [7, 15).
        let pf = parse_module(FileId(0), "a.ts", "const a: number = 1;\n");
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 1);
        let decl = &pf.decls[0];
        let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "a");
        assert_eq!(
            symbol.span,
            Span {
                file: FileId(0),
                lo: 6,
                hi: 7
            }
        );
        let annotation = decl.annotation.as_ref().expect("annotated");
        assert_eq!(annotation.text, "number");
        assert_eq!(
            annotation.span,
            Span {
                file: FileId(0),
                lo: 7,
                hi: 15
            }
        );
        let init = decl.init.as_ref().expect("initialized");
        assert_eq!(init.kind, InitKind::Number);
        assert_eq!(
            init.span,
            Span {
                file: FileId(0),
                lo: 18,
                hi: 19
            }
        );
    }

    #[test]
    fn decl_facts_cover_all_literal_kinds() {
        // Offsets cross-checked with the oxc parser; every annotation span
        // below is the colon-inclusive TSTypeAnnotation range.
        let src = "const u = 1;\n\
                   const n = other;\n\
                   const t: boolean = true;\n\
                   const z: null = null;\n\
                   const w: undefined = undefined;\n";
        let pf = parse_module(FileId(0), "k.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 5);
        // Source order is deterministic: unannotated, non-literal, then the
        // boolean/null/undefined spellings.
        let cases = [
            ("u", (6, 7), None, (InitKind::Number, (10, 11))),
            ("n", (19, 20), None, (InitKind::NonLiteral, (23, 28))),
            (
                "t",
                (36, 37),
                Some(("boolean", (37, 46))),
                (InitKind::Boolean, (49, 53)),
            ),
            (
                "z",
                (61, 62),
                Some(("null", (62, 68))),
                (InitKind::Null, (71, 75)),
            ),
            (
                "w",
                (83, 84),
                Some(("undefined", (84, 95))),
                (InitKind::Undefined, (98, 107)),
            ),
        ];
        for (decl, (name, binding, expected_ann, expected_init)) in pf.decls.iter().zip(cases) {
            let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
            assert_eq!(symbol.name, name);
            assert_eq!((symbol.span.lo, symbol.span.hi), binding);
            assert_eq!(symbol.span.file, FileId(0));
            assert_eq!(decl.annotation.is_some(), expected_ann.is_some());
            if let (Some(fact), Some((text, bounds))) = (decl.annotation.as_ref(), expected_ann) {
                assert_eq!(fact.text, text, "annotation text for {name}");
                assert_eq!((fact.span.lo, fact.span.hi), bounds);
                assert_eq!(fact.span.file, FileId(0));
            }
            let init = decl.init.as_ref().expect("initialized");
            assert_eq!(init.kind, expected_init.0, "init kind for {name}");
            assert_eq!((init.span.lo, init.span.hi), expected_init.1);
            assert_eq!(init.span.file, FileId(0));
        }
    }

    #[test]
    fn decl_facts_multi_declarator_link_each_symbol() {
        // Mirrors corpus/check-const/multi-declarator.ts without its header
        // comment; offsets cross-checked with the oxc parser.
        let pf = parse_module(
            FileId(0),
            "m.ts",
            "const first: number = 1, second: string = \"ok\", third: boolean = 42;\n",
        );
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 3);
        let cases = [
            (
                "first",
                (6, 11),
                "number",
                (11, 19),
                InitKind::Number,
                (22, 23),
            ),
            (
                "second",
                (25, 31),
                "string",
                (31, 39),
                InitKind::String,
                (42, 46),
            ),
            (
                "third",
                (48, 53),
                "boolean",
                (53, 62),
                InitKind::Number,
                (65, 67),
            ),
        ];
        for (decl, (name, binding, text, ann_bounds, kind, init_bounds)) in
            pf.decls.iter().zip(cases)
        {
            let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
            assert_eq!(symbol.name, name);
            assert_eq!((symbol.span.lo, symbol.span.hi), binding);
            let annotation = decl.annotation.as_ref().expect("annotated");
            assert_eq!(annotation.text, text);
            assert_eq!((annotation.span.lo, annotation.span.hi), ann_bounds);
            let init = decl.init.as_ref().expect("initialized");
            assert_eq!(init.kind, kind);
            assert_eq!((init.span.lo, init.span.hi), init_bounds);
        }
    }

    #[test]
    fn decl_facts_skip_non_const_and_capture_nested() {
        // `let`/`var` and functions bind symbols but emit no decl facts;
        // a const nested in a function body is still captured (the visitor
        // walks the whole program, not just top-level statements).
        let pf = parse_module(
            FileId(2),
            "n.ts",
            "function f(): void {\n  const inner: number = 2;\n  return inner;\n}\nlet l = 1;\nvar v = 2;\n",
        );
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(!pf.symbols.is_empty());
        assert_eq!(pf.decls.len(), 1);
        let decl = &pf.decls[0];
        let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "inner");
        assert_eq!((symbol.span.lo, symbol.span.hi), (29, 34));
        let annotation = decl.annotation.as_ref().expect("annotated");
        assert_eq!(annotation.text, "number");
        assert_eq!((annotation.span.lo, annotation.span.hi), (34, 42));
        let init = decl.init.as_ref().expect("initialized");
        assert_eq!(init.kind, InitKind::Number);
        assert_eq!((init.span.lo, init.span.hi), (45, 46));
    }

    #[test]
    fn decl_facts_empty_without_consts() {
        let pf = parse_module(
            FileId(3),
            "e.ts",
            "function f(a: string): string { return a; }\nlet l = 1;\nvar v = 2;\n",
        );
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(!pf.symbols.is_empty());
        assert!(pf.decls.is_empty());
    }

    #[test]
    fn decl_facts_synth50_shared_has_no_consts() {
        // Perf-corpus shape: parsing shared.ts must succeed with empty decls
        // (interface-only file). Measurement of the walk itself is deferred
        // to remote runs — no local Rust toolchain here.
        let src = include_str!("../../../corpus/perf/synth-50/shared.ts");
        let pf = parse_module(FileId(9), "shared.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(pf.decls.is_empty());
    }

    #[test]
    fn decl_facts_cover_check_const_corpus() {
        // The real const declarations the solver checks: every declarator in
        // annotated-correct.ts links to its symbol with exact spans
        // (offsets cross-checked with the oxc parser).
        let src = include_str!("../../../corpus/check-const/annotated-correct.ts");
        let pf = parse_module(FileId(0), "annotated-correct.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 5);
        let cases = [
            (
                "aNumber",
                (84, 91),
                "number",
                (91, 99),
                InitKind::Number,
                (102, 103),
            ),
            (
                "aString",
                (111, 118),
                "string",
                (118, 126),
                InitKind::String,
                (129, 133),
            ),
            (
                "aBoolean",
                (141, 149),
                "boolean",
                (149, 158),
                InitKind::Boolean,
                (161, 165),
            ),
            (
                "aNull",
                (173, 178),
                "null",
                (178, 184),
                InitKind::Null,
                (187, 191),
            ),
            (
                "anUndefined",
                (199, 210),
                "undefined",
                (210, 221),
                InitKind::Undefined,
                (224, 233),
            ),
        ];
        for (decl, (name, binding, text, ann_bounds, kind, init_bounds)) in
            pf.decls.iter().zip(cases)
        {
            let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
            assert_eq!(symbol.name, name);
            assert_eq!((symbol.span.lo, symbol.span.hi), binding);
            let annotation = decl.annotation.as_ref().expect("annotated");
            assert_eq!(annotation.text, text);
            assert_eq!((annotation.span.lo, annotation.span.hi), ann_bounds);
            let init = decl.init.as_ref().expect("initialized");
            assert_eq!(init.kind, kind);
            assert_eq!((init.span.lo, init.span.hi), init_bounds);
        }

        // Union text survives slicing (solver detects `|` itself); unknown
        // names survive verbatim; unannotated decls carry `None`.
        let union_src = include_str!("../../../corpus/check-const/union-annotation.ts");
        let union_pf = parse_module(FileId(1), "union-annotation.ts", union_src);
        assert_eq!(union_pf.decls.len(), 1);
        let union_ann = union_pf.decls[0].annotation.as_ref().expect("annotated");
        assert_eq!(union_ann.text, "number | string");
        assert_eq!((union_ann.span.lo, union_ann.span.hi), (87, 104));

        let unknown_src = include_str!("../../../corpus/check-const/unknown-annotation.ts");
        let unknown_pf = parse_module(FileId(2), "unknown-annotation.ts", unknown_src);
        assert_eq!(unknown_pf.decls.len(), 1);
        let unknown_ann = unknown_pf.decls[0].annotation.as_ref().expect("annotated");
        assert_eq!(unknown_ann.text, "Nope");
        assert_eq!((unknown_ann.span.lo, unknown_ann.span.hi), (80, 86));

        let plain_src = include_str!("../../../corpus/check-const/no-annotation.ts");
        let plain_pf = parse_module(FileId(3), "no-annotation.ts", plain_src);
        assert_eq!(plain_pf.decls.len(), 1);
        assert!(plain_pf.decls[0].annotation.is_none());
        let plain_init = plain_pf.decls[0].init.as_ref().expect("initialized");
        assert_eq!(plain_init.kind, InitKind::Number);
        assert_eq!((plain_init.span.lo, plain_init.span.hi), (85, 86));
    }

    #[test]
    fn scope_indices_are_dense_and_linked() {
        let src = "const x = 1;\nfunction f(a: string) {\n  const y = a + String(x);\n  function g() { return y; }\n}\n";
        let pf = parse_module(FileId(4), "n.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        let len = sat_u32(pf.scopes.len());
        // indices are dense root-first: exactly 0..len, each once. (A
        // constant-index bug here once pinned every scope to 0 and every
        // other assertion below still passed.)
        {
            let mut seen: Vec<u32> = pf.scopes.iter().map(|scope| scope.index).collect();
            seen.sort_unstable();
            let want: Vec<u32> = (0..len).collect();
            assert_eq!(seen, want);
        }
        // every symbol points at a real scope; every parent resolves or is root
        for symbol in &pf.symbols {
            assert!(
                symbol.scope < len,
                "symbol {} scope {} out of {}",
                symbol.name,
                symbol.scope,
                len
            );
        }
        for scope in &pf.scopes {
            assert!(
                scope.parent == u32::MAX || scope.parent < len,
                "scope {} parent {} out of {}",
                scope.index,
                scope.parent,
                len
            );
        }
        // parent chains terminate at the root within len steps
        for scope in &pf.scopes {
            let mut at = scope.index;
            for _ in 0..len {
                if at == u32::MAX {
                    break;
                }
                at = pf.scopes[usize::try_from(at).expect("dense scope index")].parent;
            }
            assert_eq!(
                at,
                u32::MAX,
                "scope {} chain does not terminate",
                scope.index
            );
        }
    }

    #[test]
    fn decl_facts_skip_destructured_bindings() {
        // Destructured declarators bind symbols but emit no decl facts:
        // only the plain `const c` below produces one, with no mis-keying
        // onto the destructured names.
        let pf = parse_module(
            FileId(5),
            "d.ts",
            "const {a} = obj;\nconst [b] = arr;\nconst c: number = 3;\n",
        );
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        let bound: Vec<&str> = pf
            .symbols
            .iter()
            .map(|symbol| symbol.name.as_str())
            .collect();
        assert!(bound.contains(&"a"), "symbols: {bound:?}");
        assert!(bound.contains(&"b"), "symbols: {bound:?}");
        assert_eq!(pf.decls.len(), 1);
        let decl = &pf.decls[0];
        let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "c");
        assert_eq!((symbol.span.lo, symbol.span.hi), (40, 41));
        let annotation = decl.annotation.as_ref().expect("annotated");
        assert_eq!(annotation.text, "number");
        assert_eq!((annotation.span.lo, annotation.span.hi), (41, 49));
        let init = decl.init.as_ref().expect("initialized");
        assert_eq!(init.kind, InitKind::Number);
        assert_eq!((init.span.lo, init.span.hi), (52, 53));
    }

    #[test]
    fn decl_facts_carry_declarator_scope() {
        // Shadowing: the inner `x` must link its own symbol AND scope, so a
        // downstream driver can resolve the inner declaration span instead
        // of the outer one (P012 scope threading).
        let pf = parse_module(
            FileId(7),
            "s.ts",
            "const x: number = 1;\nfunction f(): void {\n  const x: string = \"ok\";\n  console.log(x);\n}\n",
        );
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 2);
        let scopes: Vec<u32> = pf.decls.iter().map(|decl| decl.scope).collect();
        assert_ne!(
            scopes[0], scopes[1],
            "shadowing decls share scope: {scopes:?}"
        );
        for decl in &pf.decls {
            let symbol = &pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")];
            assert_eq!(symbol.name, "x");
            assert_eq!(
                decl.scope, symbol.scope,
                "decl scope trails its symbol's scope"
            );
        }
    }

    #[test]
    fn decl_facts_capture_export_and_for_of_consts() {
        // `export const` behaves like a plain declarator; a `for(const k of …)`
        // declarator has no initializer, so its fact carries `init: None`.
        let pf = parse_module(
            FileId(6),
            "e.ts",
            "export const e: number = 1;\nfor (const k of [1, 2]) { console.log(k); }\n",
        );
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 2);
        let first = &pf.decls[0];
        let first_symbol = &pf.symbols[usize::try_from(first.symbol).expect("dense symbol index")];
        assert_eq!(first_symbol.name, "e");
        assert_eq!((first_symbol.span.lo, first_symbol.span.hi), (13, 14));
        let first_ann = first.annotation.as_ref().expect("annotated");
        assert_eq!(first_ann.text, "number");
        assert_eq!((first_ann.span.lo, first_ann.span.hi), (14, 22));
        let first_init = first.init.as_ref().expect("initialized");
        assert_eq!(first_init.kind, InitKind::Number);
        assert_eq!((first_init.span.lo, first_init.span.hi), (25, 26));
        let second = &pf.decls[1];
        let second_symbol =
            &pf.symbols[usize::try_from(second.symbol).expect("dense symbol index")];
        assert_eq!(second_symbol.name, "k");
        assert_eq!((second_symbol.span.lo, second_symbol.span.hi), (39, 40));
        assert!(second.annotation.is_none());
        assert!(second.init.is_none());
    }

    /// Slices `src` at a fact span (the roundtrip every span below must satisfy).
    fn slice_of(src: &str, span: Span) -> &str {
        &src[span.lo as usize..span.hi as usize]
    }

    #[test]
    fn function_facts_single_return_exact_spans() {
        let src = "function add(a: number): number {\n  return 1;\n}\n";
        let pf = parse_module(FileId(0), "f.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 1);
        let fact = &pf.functions[0];
        let symbol = &pf.symbols[usize::try_from(fact.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "add");
        assert_eq!((symbol.span.lo, symbol.span.hi), (9, 12));
        assert_eq!(symbol.span.file, FileId(0));
        assert_eq!(fact.scope, symbol.scope);
        assert!(!fact.params_complex);
        assert_eq!(fact.params.len(), 1);
        assert_eq!(fact.params[0].name, "a");
        assert!(fact.params[0].annotated);
        let annotation = fact.return_annotation.as_ref().expect("annotated");
        assert_eq!(annotation.text, "number");
        assert_eq!(slice_of(src, annotation.span), ": number");
        assert_eq!(annotation.span.file, FileId(0));
        let FunctionBodyFact::SingleReturn(ret) = &fact.body else {
            panic!("expected single return, got {:?}", fact.body);
        };
        assert_eq!(ret.kind, ReturnKind::Number);
        assert_eq!(slice_of(src, ret.span), "1");
        assert!(ret.members.is_none());
    }

    #[test]
    fn function_facts_export_overload_declare_empty() {
        let src = "export function greet(name: string): string {\n  return \"ok\";\n}\n\
                   function empty(): void {}\n\
                   declare function ambient(a: number): number;\n\
                   function over(a: number): number;\n\
                   function over(a: string): string {\n  return \"ok\";\n}\n";
        let pf = parse_module(FileId(0), "o.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 5);
        let names: Vec<&str> = pf
            .functions
            .iter()
            .map(|fact| {
                pf.symbols[usize::try_from(fact.symbol).expect("dense symbol index")]
                    .name
                    .as_str()
            })
            .collect();
        assert_eq!(names, ["greet", "empty", "ambient", "over", "over"]);
        // Exported declarations are still declarations.
        let greet = &pf.functions[0];
        assert_eq!(greet.params.len(), 1);
        assert_eq!(greet.params[0].name, "name");
        assert!(greet.params[0].annotated);
        let greet_ann = greet.return_annotation.as_ref().expect("annotated");
        assert_eq!(greet_ann.text, "string");
        assert_eq!(slice_of(src, greet_ann.span), ": string");
        let FunctionBodyFact::SingleReturn(ret) = &greet.body else {
            panic!("expected single return, got {:?}", greet.body);
        };
        assert_eq!(ret.kind, ReturnKind::String);
        assert_eq!(slice_of(src, ret.span), "\"ok\"");
        // Statement-less bodies are empty, not complex.
        assert_eq!(pf.functions[1].body, FunctionBodyFact::Empty);
        let empty_ann = pf.functions[1]
            .return_annotation
            .as_ref()
            .expect("annotated");
        assert_eq!(empty_ann.text, "void");
        // Ambient declarations carry the flag on a body-less fact.
        assert_eq!(
            pf.functions[2].body,
            FunctionBodyFact::NoBody { declared: true }
        );
        // Overload signatures are body-less without the flag; the
        // implementation is a normal single return.
        assert_eq!(
            pf.functions[3].body,
            FunctionBodyFact::NoBody { declared: false }
        );
        let FunctionBodyFact::SingleReturn(over) = &pf.functions[4].body else {
            panic!("expected single return, got {:?}", pf.functions[4].body);
        };
        assert_eq!(over.kind, ReturnKind::String);
    }

    #[test]
    fn function_facts_complex_shapes() {
        let src = "function multi(n: number): number {\n  return 1;\n  return 2;\n}\n\
                   function branch(flag: boolean): number {\n  if (flag) {\n    return 1;\n  }\n  return 2;\n}\n\
                   function bare(n: number): void {\n  return;\n}\n\
                   function silent(n: number): void {\n  console.log(n);\n}\n\
                   function ident(n: number): number {\n  return n;\n}\n\
                   function outer(): number {\n  function inner(): number {\n    return 2;\n  }\n  return 1;\n}\n";
        let pf = parse_module(FileId(0), "c.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        // Visitor order is pre-order: `inner` follows its enclosing `outer`.
        assert_eq!(pf.functions.len(), 7);
        let names: Vec<&str> = pf
            .functions
            .iter()
            .map(|fact| {
                pf.symbols[usize::try_from(fact.symbol).expect("dense symbol index")]
                    .name
                    .as_str()
            })
            .collect();
        assert_eq!(
            names,
            ["multi", "branch", "bare", "silent", "ident", "outer", "inner"]
        );
        for fact in pf.functions.iter().take(4) {
            assert_eq!(fact.body, FunctionBodyFact::Complex);
        }
        // A single non-literal return stays a single return (the solver, not
        // the adapter, declines it).
        let FunctionBodyFact::SingleReturn(ident) = &pf.functions[4].body else {
            panic!("expected single return, got {:?}", pf.functions[4].body);
        };
        assert_eq!(ident.kind, ReturnKind::NonLiteral);
        assert_eq!(slice_of(src, ident.span), "n");
        assert!(ident.members.is_none());
        // An inner declaration is a statement: the outer body is complex
        // while the nested declaration still gets its own fact.
        assert_eq!(pf.functions[5].body, FunctionBodyFact::Complex);
        let FunctionBodyFact::SingleReturn(inner) = &pf.functions[6].body else {
            panic!("expected single return, got {:?}", pf.functions[6].body);
        };
        assert_eq!(inner.kind, ReturnKind::Number);
        assert_eq!(slice_of(src, inner.span), "2");
    }

    #[test]
    fn function_facts_object_return_members() {
        let src = "function point(): { x: number; done: boolean } {\n  return { x: 1, done: false };\n}\n";
        let pf = parse_module(FileId(0), "p.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 1);
        let fact = &pf.functions[0];
        assert!(fact.params.is_empty());
        assert!(!fact.params_complex);
        let annotation = fact.return_annotation.as_ref().expect("annotated");
        assert_eq!(annotation.text, "{ x: number; done: boolean }");
        assert_eq!(
            slice_of(src, annotation.span),
            ": { x: number; done: boolean }"
        );
        let FunctionBodyFact::SingleReturn(ret) = &fact.body else {
            panic!("expected single return, got {:?}", fact.body);
        };
        // Object returns park the shape in `members`, not `kind`.
        assert_eq!(ret.kind, ReturnKind::NonLiteral);
        assert_eq!(slice_of(src, ret.span), "{ x: 1, done: false }");
        let members = ret.members.as_ref().expect("object members");
        assert_eq!(members.len(), 2);
        assert_eq!(members[0].name, "x");
        assert_eq!(members[0].kind, ReturnKind::Number);
        assert_eq!(slice_of(src, members[0].span), "1");
        assert_eq!(members[1].name, "done");
        assert_eq!(members[1].kind, ReturnKind::Boolean(false));
        assert_eq!(slice_of(src, members[1].span), "false");
    }

    #[test]
    fn function_facts_object_spread_is_complex() {
        let src =
            "function spread(base: { x: number }): { x: number } {\n  return { ...base };\n}\n";
        let pf = parse_module(FileId(0), "s.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 1);
        assert_eq!(pf.functions[0].body, FunctionBodyFact::Complex);
    }

    #[test]
    fn function_facts_params_and_excluded_shapes() {
        let src = "function mixed(a: number, b, ...rest: string[]): number {\n  return 1;\n}\n\
                   function destructured({x}: { x: number }): number {\n  return 1;\n}\n\
                   const arrow = (n: number): number => n;\n\
                   let expr = function named(n: number): number {\n  return n;\n};\n\
                   const obj = { pick(n: number): number { return n; } };\n\
                   class Box { get(n: number): number { return n; } }\n";
        let pf = parse_module(FileId(0), "x.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        // Arrows, function expressions, and methods bind symbols but emit no
        // function facts.
        assert_eq!(pf.functions.len(), 2);
        let mixed = &pf.functions[0];
        assert!(!mixed.params_complex);
        let names: Vec<&str> = mixed
            .params
            .iter()
            .map(|param| param.name.as_str())
            .collect();
        assert_eq!(names, ["a", "b", "rest"]);
        let annotated: Vec<bool> = mixed.params.iter().map(|param| param.annotated).collect();
        assert_eq!(annotated, [true, false, true]);
        // Call-checker enabling: annotation text plus optional/rest markers.
        let texts: Vec<Option<&str>> = mixed
            .params
            .iter()
            .map(|param| param.annotation_text.as_deref())
            .collect();
        assert_eq!(texts, [Some("number"), None, Some("string[]")]);
        let optional: Vec<bool> = mixed.params.iter().map(|param| param.optional).collect();
        assert_eq!(optional, [false, false, false]);
        let rests: Vec<bool> = mixed.params.iter().map(|param| param.is_rest).collect();
        assert_eq!(rests, [false, false, true]);
        let destructured = &pf.functions[1];
        assert!(destructured.params_complex);
        assert!(destructured.params.is_empty());
    }

    #[test]
    fn function_facts_optional_and_defaulted_mark_range() {
        let src =
            "function opt(a: number, b?: number, c: string = \"d\"): number {\n  return 1;\n}\n";
        let pf = parse_module(FileId(0), "o.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 1);
        let fact = &pf.functions[0];
        assert!(!fact.params_complex);
        let names: Vec<&str> = fact
            .params
            .iter()
            .map(|param| param.name.as_str())
            .collect();
        assert_eq!(names, ["a", "b", "c"]);
        let optional: Vec<bool> = fact.params.iter().map(|param| param.optional).collect();
        // `?` and defaulted alike widen arity to a range: both decline.
        assert_eq!(optional, [false, true, true]);
        let texts: Vec<Option<&str>> = fact
            .params
            .iter()
            .map(|param| param.annotation_text.as_deref())
            .collect();
        assert_eq!(texts, [Some("number"), Some("number"), Some("string")]);
        assert!(!fact.params.iter().any(|param| param.is_rest));
    }

    #[test]
    fn function_facts_type_params_plain_single() {
        // `id<T>` records its one plain name with a clear flag; the
        // non-generic `plain` records nothing.
        let src = "function id<T>(x: T): T {\n  return x;\n}\nfunction plain(a: number): number {\n  return 1;\n}\n";
        let pf = parse_module(FileId(0), "g.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 2);
        let generic = &pf.functions[0];
        assert_eq!(
            generic
                .type_params
                .iter()
                .map(|param| param.name.as_str())
                .collect::<Vec<&str>>(),
            ["T"]
        );
        assert!(!generic.type_params_complex);
        let plain = &pf.functions[1];
        assert!(plain.type_params.is_empty());
        assert!(!plain.type_params_complex);
    }

    #[test]
    fn function_facts_type_params_complex_shapes() {
        // Constraints, defaults, and `const`/`in`/`out` modifiers all set the
        // flag while still recording their names; multi-parameter lists
        // record every name (the solver declines on count, never miscount).
        let src = "function constrained<T extends string>(x: T): T {\n  return x;\n}\n\
                   function defaulted<T = number>(x: T): T {\n  return x;\n}\n\
                   function consted<const T>(x: T): T {\n  return x;\n}\n\
                   function pair<T, U>(x: T, y: U): T {\n  return x;\n}\n";
        let pf = parse_module(FileId(0), "c.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 4);
        let names: Vec<Vec<&str>> = pf
            .functions
            .iter()
            .map(|fact| {
                fact.type_params
                    .iter()
                    .map(|param| param.name.as_str())
                    .collect()
            })
            .collect();
        assert_eq!(names, vec![vec!["T"], vec!["T"], vec!["T"], vec!["T", "U"]]);
        for fact in &pf.functions[..3] {
            assert!(
                fact.type_params_complex,
                "complex flag for {:?}",
                fact.type_params
            );
        }
        // Multi-parameter lists record every name without the flag: the
        // solver declines on count, never miscount.
        assert!(!pf.functions[3].type_params_complex);
    }

    #[test]
    fn call_facts_direct_call_exact_spans() {
        // Offsets hand-counted (`add(1, "ok");` starts at 59: `add` at
        // 59..62, `1` at 63, `"ok"` at 66..70, whole call 59..71).
        let src = "function add(a: number, b: string): number {\n  return 1;\n}\nadd(1, \"ok\");\n";
        let pf = parse_module(FileId(0), "c.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.calls.len(), 1);
        let call = &pf.calls[0];
        assert_eq!(call.callee, "add");
        assert_eq!((call.callee_span.lo, call.callee_span.hi), (59, 62));
        assert_eq!(call.callee_span.file, FileId(0));
        assert_eq!((call.span.lo, call.span.hi), (59, 71));
        assert_eq!(call.span.file, FileId(0));
        assert_eq!(slice_of(src, call.callee_span), "add");
        assert_eq!(slice_of(src, call.span), "add(1, \"ok\")");
        assert_eq!(call.args.len(), 2);
        assert_eq!(call.args[0].kind, CallArgKind::Number);
        assert_eq!((call.args[0].span.lo, call.args[0].span.hi), (63, 64));
        assert_eq!(slice_of(src, call.args[0].span), "1");
        assert_eq!(call.args[1].kind, CallArgKind::String);
        assert_eq!((call.args[1].span.lo, call.args[1].span.hi), (66, 70));
        assert_eq!(slice_of(src, call.args[1].span), "\"ok\"");
    }

    #[test]
    fn call_facts_cover_all_arg_kinds() {
        let src = "f(1, \"ok\", true, null, undefined, other, { x: 1 }, g(2));\n";
        let pf = parse_module(FileId(0), "k.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        // Pre-order: the outer `f(...)` fact lands before the nested `g(2)`.
        assert_eq!(pf.calls.len(), 2);
        let outer = &pf.calls[0];
        assert_eq!(outer.callee, "f");
        let kinds: Vec<CallArgKind> = outer.args.iter().map(|arg| arg.kind).collect();
        assert_eq!(
            kinds,
            [
                CallArgKind::Number,
                CallArgKind::String,
                CallArgKind::Boolean,
                CallArgKind::Null,
                CallArgKind::Undefined,
                CallArgKind::NonLiteral,
                CallArgKind::NonLiteral,
                CallArgKind::NonLiteral,
            ]
        );
        for arg in &outer.args {
            assert_eq!(arg.span.file, FileId(0));
            assert!(arg.span.lo < arg.span.hi);
        }
        let inner = &pf.calls[1];
        assert_eq!(inner.callee, "g");
        assert_eq!(inner.args.len(), 1);
        assert_eq!(inner.args[0].kind, CallArgKind::Number);
    }

    #[test]
    fn call_facts_skip_methods_optionals_spreads() {
        // Methods, optional chains, and spreads bind symbols but emit no call
        // facts: only the final direct `add(1, 2)` does. The unresolved
        // `missing` keeps the skip honest (no decl to mis-resolve to).
        let src = "function add(a: number, b: number): number {\n  return 1;\n}\n\
                   const obj = { pick(n: number): number { return n; } };\n\
                   obj.pick(1, 2);\nadd?.(1);\nadd(...[1, 2]);\nmissing(1);\nadd(1, 2);\n";
        let pf = parse_module(FileId(0), "s.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.calls.len(), 2);
        let callees: Vec<&str> = pf.calls.iter().map(|call| call.callee.as_str()).collect();
        assert_eq!(callees, ["missing", "add"]);
        let last = &pf.calls[1];
        assert_eq!(last.args.len(), 2);
    }

    #[test]
    fn call_facts_skip_tagged_new_super_import() {
        // Tagged templates, `new`, `super()`, and `import()` never reach
        // `visit_call_expression` (or fail the identifier gate): no facts,
        // never mis-recorded. The trailing direct call proves the walker
        // kept going.
        let src = "function add(a: number, b: number): number {\n  return 1;\n}\n\
                   const tag = (s: string) => s;\n\
                   tag`hi`;\n\
                   new Date();\n\
                   class C extends Date {\n  constructor() {\n    super();\n  }\n}\n\
                   add(1, 2);\n";
        let pf = parse_module(FileId(0), "s.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.calls.len(), 1);
        assert_eq!(pf.calls[0].callee, "add");
        assert_eq!(pf.calls[0].args.len(), 2);
    }

    #[test]
    fn call_facts_skip_dynamic_import() {
        // `import("x")` is an import expression, not a call: no fact. Kept
        // separate because it parses as a distinct AST node (`ImportExpression`).
        let src = "async function load(): Promise<void> {\n  await import(\"./m\");\n}\n";
        let pf = parse_module(FileId(0), "s.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(pf.calls.is_empty());
    }

    #[test]
    fn guard_facts_simple_eq_with_else_exact_spans() {
        // Offsets hand-counted: `x` at 11..12, `"string"` at 17..25, the
        // then block at 27..51, the else block at 57..81.
        let src =
            "if (typeof x === \"string\") { const a: string = x; } else { const b: number = x; }\n";
        let pf = parse_module(FileId(0), "g.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.decls.len(), 2);
        assert!(pf.decline_regions.is_empty());
        assert_eq!(pf.guards.len(), 1);
        let guard = &pf.guards[0];
        assert_eq!(guard.target, "x");
        assert_eq!((guard.target_span.lo, guard.target_span.hi), (11, 12));
        assert_eq!(slice_of(src, guard.target_span), "x");
        assert_eq!(guard.matched, "string");
        assert!(!guard.negated);
        assert_eq!((guard.then_span.lo, guard.then_span.hi), (27, 51));
        assert_eq!(slice_of(src, guard.then_span), "{ const a: string = x; }");
        let else_span = guard.else_span.expect("else branch");
        assert_eq!((else_span.lo, else_span.hi), (57, 81));
        assert_eq!(slice_of(src, else_span), "{ const b: number = x; }");
        assert!(!guard.early_return);
        assert_eq!((guard.if_span.lo, guard.if_span.hi), (0, 81));
        assert_eq!(guard.if_span.file, FileId(0));
    }

    #[test]
    fn guard_facts_early_return_exact_spans() {
        // `if` at 23..57 inside `f`; the bare `return;` at 50..57 marks the
        // early-return shape, so code after the statement refines.
        let src = "function f(): void {\n  if (typeof x !== \"string\") return;\n}\n";
        let pf = parse_module(FileId(0), "e.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.functions.len(), 1);
        assert_eq!(pf.functions[0].body, FunctionBodyFact::Complex);
        assert!(pf.decline_regions.is_empty());
        assert_eq!(pf.guards.len(), 1);
        let guard = &pf.guards[0];
        assert_eq!(guard.target, "x");
        assert_eq!((guard.target_span.lo, guard.target_span.hi), (34, 35));
        assert_eq!(guard.matched, "string");
        assert!(guard.negated);
        assert_eq!((guard.then_span.lo, guard.then_span.hi), (50, 57));
        assert_eq!(slice_of(src, guard.then_span), "return;");
        assert!(guard.else_span.is_none());
        assert!(guard.early_return);
        assert_eq!((guard.if_span.lo, guard.if_span.hi), (23, 57));
    }

    #[test]
    fn guard_facts_decline_complex_nested_loose_else_if() {
        let src = "if (a && b) { const c = 1; }\n\
                   if (typeof x === \"string\") { if (typeof y === \"number\") { const d = 1; } }\n\
                   if (typeof x == \"string\") { const e = 1; }\n\
                   if (typeof x === \"string\") { const f = 1; } else if (typeof x === \"number\") { const g = 1; }\n\
                   if (typeof y.z === \"string\") { const h = 1; }\n\
                   if (typeof x === y) { const i = 1; }\n";
        let pf = parse_module(FileId(0), "d.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        // Only the outer nested guard refines; every other shape declines.
        assert_eq!(pf.guards.len(), 1);
        assert_eq!(pf.guards[0].target, "x");
        assert!(pf.guards[0].else_span.is_none());
        assert!(!pf.guards[0].early_return);
        assert_eq!(pf.decline_regions.len(), 7);
        let reasons: Vec<&str> = pf
            .decline_regions
            .iter()
            .map(|region| region.reason.as_str())
            .collect();
        assert!(
            reasons[0].contains("simple typeof"),
            "complex condition: {}",
            reasons[0]
        );
        assert!(
            reasons[1].contains("nested guard"),
            "nested guard: {}",
            reasons[1]
        );
        assert!(
            reasons[2].contains("simple typeof"),
            "loose equality: {}",
            reasons[2]
        );
        assert!(
            reasons[3].contains("else-if"),
            "else-if chain: {}",
            reasons[3]
        );
        assert!(
            reasons[4].contains("nested guard"),
            "else-if inner link: {}",
            reasons[4]
        );
        assert!(
            reasons[5].contains("simple typeof"),
            "member target: {}",
            reasons[5]
        );
        assert!(
            reasons[6].contains("simple typeof"),
            "identifier comparand: {}",
            reasons[6]
        );
        for region in &pf.decline_regions {
            assert_eq!(region.span.file, FileId(0));
            assert!(region.span.lo < region.span.hi);
            assert!(slice_of(src, region.span).starts_with("if "));
        }
    }

    #[test]
    fn guard_facts_early_return_variants() {
        // Swapped operands plus a block-wrapped valued return still mark
        // early-return; so does a bare `throw` (both refine after, probed
        // tsc 7.0.2).
        let src = "function f(): void {\n  if (\"string\" !== typeof x) { return 1; }\n  if (typeof x !== \"string\") throw new Error();\n}\n";
        let pf = parse_module(FileId(0), "v.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(pf.decline_regions.is_empty());
        assert_eq!(pf.guards.len(), 2);
        let first = &pf.guards[0];
        assert_eq!(first.target, "x");
        assert_eq!((first.target_span.lo, first.target_span.hi), (47, 48));
        assert_eq!(first.matched, "string");
        assert!(first.negated);
        assert_eq!((first.then_span.lo, first.then_span.hi), (50, 63));
        assert_eq!(slice_of(src, first.then_span), "{ return 1; }");
        assert!(first.early_return);
        assert_eq!((first.if_span.lo, first.if_span.hi), (23, 63));
        let second = &pf.guards[1];
        assert_eq!(second.target, "x");
        assert_eq!((second.target_span.lo, second.target_span.hi), (77, 78));
        assert!(second.negated);
        assert_eq!(slice_of(src, second.then_span), "throw new Error();");
        assert!(second.early_return);
        assert_eq!((second.if_span.lo, second.if_span.hi), (66, 111));
    }

    #[test]
    fn guard_facts_parenthesized_condition_refines() {
        // One paren layer around the whole condition is transparent.
        let src = "if ((typeof x === \"string\")) { const a = 1; }\n";
        let pf = parse_module(FileId(0), "p.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(pf.decline_regions.is_empty());
        assert_eq!(pf.guards.len(), 1);
        assert_eq!(pf.guards[0].target, "x");
        assert!(!pf.guards[0].negated);
    }

    #[test]
    fn guard_facts_nested_function_boundary_declines() {
        // `g` is nested in `f`: its whole body declines (closures reset
        // narrowing — probed tsc 7.0.2), while no guard fact fires.
        let src =
            "function f(): void {\n  function g(): void {\n    const c: number = x;\n  }\n}\n";
        let pf = parse_module(FileId(0), "n.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert!(pf.guards.is_empty());
        assert_eq!(pf.decline_regions.len(), 1);
        let region = &pf.decline_regions[0];
        assert_eq!((region.span.lo, region.span.hi), (23, 72));
        assert_eq!(
            slice_of(src, region.span),
            "function g(): void {\n    const c: number = x;\n  }"
        );
        assert!(region.reason.contains("closure"));
    }

    #[test]
    fn interface_facts_primitive_members_exact_spans() {
        // Offsets hand-counted: `interface` at 0..9, `Point` at 10..15, `{`
        // at 16, `x` at 18, `label` at 29..34, `}` at 44.
        let src = "interface Point { x: number; label: string; }\n";
        let pf = parse_module(FileId(0), "i.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.interfaces.len(), 1);
        let fact = &pf.interfaces[0];
        assert_eq!(fact.name, "Point");
        assert_eq!((fact.span.lo, fact.span.hi), (0, 45));
        assert_eq!(
            slice_of(src, fact.span),
            "interface Point { x: number; label: string; }"
        );
        let symbol = &pf.symbols[usize::try_from(fact.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "Point");
        assert_eq!((symbol.span.lo, symbol.span.hi), (10, 15));
        assert_eq!(fact.scope, symbol.scope);
        assert_eq!(fact.members.len(), 2);
        let first = &fact.members[0];
        assert_eq!(first.name, "x");
        assert_eq!(first.annotation_text.as_deref(), Some("number"));
        assert!(first.complex_reason.is_none());
        assert_eq!(first.span.lo, 18);
        assert!(first.span.lo < first.span.hi);
        assert_eq!(first.span.file, FileId(0));
        assert!(slice_of(src, first.span).starts_with("x: number"));
        let second = &fact.members[1];
        assert_eq!(second.name, "label");
        assert_eq!(second.annotation_text.as_deref(), Some("string"));
        assert!(second.complex_reason.is_none());
        assert_eq!(second.span.lo, 29);
        assert!(slice_of(src, second.span).starts_with("label: string"));
        assert!(fact.heritage.is_empty());
        assert!(!fact.has_type_params);
    }

    #[test]
    fn interface_facts_complex_members_carry_reasons() {
        let src = "interface M { run(n: number): string; }\n\
                   interface O { a: number; b?: string; }\n\
                   interface I { [key: string]: number; }\n\
                   interface C { (): void; }\n\
                   interface D extends Base { a: number; }\n\
                   interface G<T> { a: T; }\n\
                   interface R { readonly x: number; }\n\
                   export interface E { a: number; }\n\
                   declare interface A { a: number; }\n";
        let pf = parse_module(FileId(0), "c.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.interfaces.len(), 9);
        let names: Vec<&str> = pf
            .interfaces
            .iter()
            .map(|fact| fact.name.as_str())
            .collect();
        assert_eq!(names, ["M", "O", "I", "C", "D", "G", "R", "E", "A"]);
        // Method signatures decline with their name in the reason.
        assert_eq!(pf.interfaces[0].members.len(), 1);
        assert_eq!(pf.interfaces[0].members[0].name, "run");
        assert!(pf.interfaces[0].members[0]
            .complex_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("method") && reason.contains("run")));
        // Plain members stay checkable; optional members decline.
        assert!(pf.interfaces[1].members[0].complex_reason.is_none());
        assert_eq!(
            pf.interfaces[1].members[0].annotation_text.as_deref(),
            Some("number")
        );
        assert_eq!(pf.interfaces[1].members[1].name, "b");
        assert!(pf.interfaces[1].members[1]
            .complex_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("optional")));
        // Index signatures keep their parameter name for the reason.
        assert_eq!(pf.interfaces[2].members[0].name, "key");
        assert!(pf.interfaces[2].members[0]
            .complex_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("index")));
        // Keyless shapes use fixed descriptors, never skipped.
        assert_eq!(pf.interfaces[3].members[0].name, "call signature");
        assert!(pf.interfaces[3].members[0]
            .complex_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("call")));
        // Heritage records the parent name; members stay checkable.
        assert_eq!(pf.interfaces[4].heritage.len(), 1);
        assert_eq!(pf.interfaces[4].heritage[0].name, "Base");
        assert!(pf.interfaces[4].members[0].complex_reason.is_none());
        // Generic parameter lists set the flag; the member itself still records.
        assert!(pf.interfaces[5].has_type_params);
        assert_eq!(
            pf.interfaces[5].members[0].annotation_text.as_deref(),
            Some("T")
        );
        assert!(pf.interfaces[5].members[0].complex_reason.is_none());
        // `readonly` is not structural: the member stays checkable.
        assert!(pf.interfaces[6].members[0].complex_reason.is_none());
        assert_eq!(
            pf.interfaces[6].members[0].annotation_text.as_deref(),
            Some("number")
        );
        // Exported and ambient forms emit facts like plain declarations.
        for fact in pf.interfaces.iter().skip(7) {
            assert_eq!(fact.members.len(), 1);
            assert!(fact.members[0].complex_reason.is_none());
            assert!(fact.heritage.is_empty());
            assert!(!fact.has_type_params);
        }
        for fact in &pf.interfaces {
            assert_eq!(fact.span.file, FileId(0));
            assert!(fact.span.lo < fact.span.hi);
        }
    }

    #[test]
    fn interface_facts_merged_value_links_one_symbol() {
        // `interface Foo` plus `const Foo` pre-merge in oxc (see the
        // module-level merge note): one symbol at the first declaration, no
        // decl fact for the const (exact `(name, start)` miss).
        let src = "interface Foo { a: string; }\nconst Foo = 42;\n";
        let pf = parse_module(FileId(0), "m.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        let foos: Vec<_> = pf.symbols.iter().filter(|s| s.name == "Foo").collect();
        assert_eq!(foos.len(), 1, "merged pair surfaces as one symbol");
        assert_eq!((foos[0].span.lo, foos[0].span.hi), (10, 13));
        assert_eq!(pf.interfaces.len(), 1);
        let fact = &pf.interfaces[0];
        assert_eq!(fact.name, "Foo");
        assert_eq!((fact.span.lo, fact.span.hi), (0, 28));
        let symbol = &pf.symbols[usize::try_from(fact.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "Foo");
        assert_eq!(fact.scope, symbol.scope);
        assert_eq!(fact.members.len(), 1);
        assert_eq!(fact.members[0].name, "a");
        assert!(fact.members[0].complex_reason.is_none());
        assert!(pf.decls.is_empty(), "merged const emits no decl fact");
    }

    #[test]
    fn enum_facts_record_literal_values_and_auto_increment() {
        let src = "enum Color { Red, Green, Blue }\n\
                   enum Base { A = 5, B, C }\n\
                   enum SN { \"kebab-key\" = 3 }\n";
        let pf = parse_module(FileId(0), "e.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.enums.len(), 3);
        let color = &pf.enums[0];
        assert_eq!(color.name, "Color");
        assert_eq!(slice_of(src, color.span), "enum Color { Red, Green, Blue }");
        assert!(!color.is_const && !color.declared && !color.exported);
        let symbol = &pf.symbols[usize::try_from(color.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "Color");
        assert_eq!(color.scope, symbol.scope);
        let values: Vec<(&str, EnumValueKind)> = color
            .members
            .iter()
            .map(|member| (member.name.as_str(), member.value.clone()))
            .collect();
        assert_eq!(
            values,
            [
                ("Red", EnumValueKind::Number(0.0)),
                ("Green", EnumValueKind::Number(1.0)),
                ("Blue", EnumValueKind::Number(2.0)),
            ]
        );
        let base = &pf.enums[1];
        assert_eq!(base.name, "Base");
        let values: Vec<f64> = base
            .members
            .iter()
            .map(|member| match member.value {
                EnumValueKind::Number(found) => found,
                ref other => panic!("expected number, got {other:?}"),
            })
            .collect();
        assert_eq!(values, [5.0, 6.0, 7.0]);
        // String-literal member names record verbatim and stay checkable.
        let named = &pf.enums[2];
        assert_eq!(named.members.len(), 1);
        assert_eq!(named.members[0].name, "kebab-key");
        assert_eq!(named.members[0].value, EnumValueKind::Number(3.0));
        for fact in &pf.enums {
            assert_eq!(fact.span.file, FileId(0));
            assert!(fact.span.lo < fact.span.hi);
        }
    }

    #[test]
    fn enum_facts_record_strings_and_decline_computed() {
        let src = "enum Str { A = \"a\", B = \"b\" }\n\
                   const K = 10;\n\
                   enum Comp { X = K, Y = -1, Z }\n\
                   enum AfterStr { S = \"s\", T }\n";
        let pf = parse_module(FileId(0), "c.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.enums.len(), 3);
        let strings = &pf.enums[0];
        assert_eq!(
            strings.members[0].value,
            EnumValueKind::String("a".to_owned())
        );
        assert_eq!(
            strings.members[1].value,
            EnumValueKind::String("b".to_owned())
        );
        // Identifier and unary initializers are computed with reasons, and a
        // bare member after them cannot auto-increment, so it declines too.
        let computed = &pf.enums[1];
        assert_eq!(computed.members.len(), 3);
        for member in &computed.members {
            let EnumValueKind::Computed { reason } = &member.value else {
                panic!("expected computed, got {:?}", member.value);
            };
            assert!(
                reason.contains("outside the subset"),
                "reason for {}: {reason}",
                member.name
            );
        }
        // A bare member after a string member declines (no numeric base).
        let after = &pf.enums[2];
        assert_eq!(
            after.members[0].value,
            EnumValueKind::String("s".to_owned())
        );
        let EnumValueKind::Computed { reason } = &after.members[1].value else {
            panic!("expected computed, got {:?}", after.members[1].value);
        };
        assert!(reason.contains("auto-increment"), "reason: {reason}");
    }

    #[test]
    fn enum_facts_carry_const_declare_export_flags() {
        let src = "const enum CE { X }\ndeclare enum AE { A }\nexport enum EE { E }\n";
        let pf = parse_module(FileId(0), "f.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.enums.len(), 3);
        assert!(pf.enums[0].is_const && !pf.enums[0].declared && !pf.enums[0].exported);
        assert!(!pf.enums[1].is_const && pf.enums[1].declared && !pf.enums[1].exported);
        assert!(!pf.enums[2].is_const && !pf.enums[2].declared && pf.enums[2].exported);
        // Ambient members still record (the solver declines them, never skips).
        assert_eq!(pf.enums[1].members.len(), 1);
        assert_eq!(pf.enums[1].members[0].value, EnumValueKind::Number(0.0));
    }

    #[test]
    fn enum_facts_decline_computed_names() {
        let pf = parse_module(FileId(0), "w.ts", "enum Weird { [\"a-b\"] = 1 }\n");
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.enums.len(), 1);
        assert_eq!(pf.enums[0].members.len(), 1);
        let EnumValueKind::Computed { reason } = &pf.enums[0].members[0].value else {
            panic!("expected computed, got {:?}", pf.enums[0].members[0].value);
        };
        assert!(reason.contains("member name"), "reason: {reason}");
    }

    #[test]
    fn namespace_facts_scope_members_and_body_scope() {
        let src = "namespace NS { export const VAL = 1; export enum Dir { Up } enum Priv { A } }\n\
                   const y: number = NS.VAL;\n";
        let pf = parse_module(FileId(0), "n.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.namespaces.len(), 1);
        let fact = &pf.namespaces[0];
        assert_eq!(fact.name, "NS");
        assert!(!fact.declared && !fact.exported);
        assert!(fact.span.lo < fact.span.hi);
        assert_eq!(fact.span.file, FileId(0));
        let symbol = &pf.symbols[usize::try_from(fact.symbol).expect("dense symbol index")];
        assert_eq!(symbol.name, "NS");
        assert_eq!(fact.scope, symbol.scope);
        // The body scope is a real child holding the member symbols.
        assert_ne!(fact.body_scope, u32::MAX, "body scope resolved");
        let body = &pf.scopes[usize::try_from(fact.body_scope).expect("dense scope index")];
        assert_eq!(body.parent, fact.scope);
        for name in ["VAL", "Dir", "Priv"] {
            let member = pf.symbols.iter().find(|s| s.name == name).expect(name);
            assert_eq!(
                member.scope, fact.body_scope,
                "member {name} scoped in body"
            );
        }
        // Declarations inside are visited normally with real facts.
        assert!(pf.decls.iter().any(|decl| {
            pf.symbols[usize::try_from(decl.symbol).expect("dense symbol index")].name == "VAL"
        }));
        // Only `export`-wrapped members list as exported (`Priv` hides).
        assert!(fact.exported_members.contains(&"VAL".to_owned()));
        assert!(fact.exported_members.contains(&"Dir".to_owned()));
        assert!(!fact.exported_members.contains(&"Priv".to_owned()));
        let dir = pf
            .enums
            .iter()
            .find(|fact| fact.name == "Dir")
            .expect("Dir fact");
        assert!(dir.exported);
        assert_eq!(dir.scope, fact.body_scope);
        let priv_enum = pf
            .enums
            .iter()
            .find(|fact| fact.name == "Priv")
            .expect("Priv fact");
        assert!(!priv_enum.exported);
    }

    #[test]
    fn namespace_facts_nest_and_track_exported() {
        let src = "namespace Outer { export namespace Inner { export const V = 2; } }\n\
                   namespace Empty {}\n\
                   declare namespace Ambient { const A: number; }\n\
                   module M { export const W = 1; }\n";
        let pf = parse_module(FileId(0), "m.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.namespaces.len(), 5);
        let outer = &pf.namespaces[0];
        let inner = &pf.namespaces[1];
        assert_eq!(
            (outer.name.as_str(), inner.name.as_str()),
            ("Outer", "Inner")
        );
        assert!(!outer.exported && inner.exported);
        assert_ne!(outer.body_scope, u32::MAX);
        assert_ne!(inner.body_scope, u32::MAX);
        // The nested block lives inside the outer body scope.
        assert_eq!(inner.scope, outer.body_scope);
        let inner_body = &pf.scopes[usize::try_from(inner.body_scope).expect("dense scope index")];
        assert_eq!(inner_body.parent, inner.scope);
        let vee = pf.symbols.iter().find(|s| s.name == "V").expect("V symbol");
        assert_eq!(vee.scope, inner.body_scope);
        // Exported members attribute to the innermost block.
        assert!(outer.exported_members.contains(&"Inner".to_owned()));
        assert!(inner.exported_members.contains(&"V".to_owned()));
        // Empty blocks have no member symbols, so no body scope.
        assert_eq!(pf.namespaces[2].name, "Empty");
        assert_eq!(pf.namespaces[2].body_scope, u32::MAX);
        // Ambient and `module`-keyword forms record like plain blocks.
        assert!(pf.namespaces[3].declared && !pf.namespaces[3].exported);
        assert_eq!(pf.namespaces[3].name, "Ambient");
        assert_eq!(pf.namespaces[4].name, "M");
        assert!(!pf.namespaces[4].declared);
        assert_ne!(pf.namespaces[4].body_scope, u32::MAX);
        for fact in &pf.namespaces {
            assert_eq!(fact.span.file, FileId(0));
            assert!(fact.span.lo < fact.span.hi);
        }
    }

    #[test]
    fn interface_facts_track_exported() {
        let src = "interface Top { a: number; }\n\
                   namespace NS { export interface Pub { x: number; } interface Hidden { y: number; } }\n";
        let pf = parse_module(FileId(0), "i.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.interfaces.len(), 3);
        assert!(!pf.interfaces[0].exported);
        assert!(pf.interfaces[1].exported);
        assert!(!pf.interfaces[2].exported);
        for fact in &pf.interfaces {
            assert!(fact.members[0].complex_reason.is_none());
        }
    }

    #[test]
    fn namespace_facts_list_all_exported_member_kinds() {
        // Every exported declaration kind attributes its name (hidden ones
        // list nowhere); `export { C }` specifier lists are not wrappers.
        let src = "namespace NS { export const C = 1; export let L = 2; export function F(): void {} export class K {} export type T = number; export enum E { A } export interface I { x: number; } export namespace N {} const Hid = 3; }\n";
        let pf = parse_module(FileId(0), "k.ts", src);
        assert!(pf.errors.is_empty(), "errors: {:?}", pf.errors);
        assert_eq!(pf.namespaces.len(), 2);
        let fact = &pf.namespaces[0];
        assert_eq!(fact.name, "NS");
        for name in ["C", "L", "F", "K", "T", "E", "I", "N"] {
            assert!(
                fact.exported_members.contains(&name.to_owned()),
                "missing {name}: {:?}",
                fact.exported_members
            );
        }
        assert!(!fact.exported_members.contains(&"Hid".to_owned()));
        assert_eq!(pf.namespaces[1].name, "N");
    }
}
