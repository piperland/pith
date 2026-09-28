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

use oxc_allocator::Allocator;
use oxc_ast::ast::{
    BindingPattern, Expression, Function, FunctionBody, FunctionType, ObjectPropertyKind, Program,
    PropertyKey, PropertyKind, Statement, VariableDeclaration, VariableDeclarationKind,
    VariableDeclarator,
};
use oxc_ast_visit::{walk, Visit};
use oxc_parser::Parser;
use oxc_semantic::{ScopeFlags, SemanticBuilder};
use oxc_span::{GetSpan, SourceType};
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
    /// Raw return annotation text + span; `None` means unannotated.
    pub return_annotation: Option<AnnotationFact>,
    /// Body shape; only [`FunctionBodyFact::SingleReturn`] is checkable.
    pub body: FunctionBodyFact,
}

/// One identifier parameter: its name plus whether it carries a type
/// annotation.
///
/// `annotated` is what the solver gates on (unannotated parameters are
/// outside the subset); the annotation text itself is not needed downstream
/// and is not recorded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionParamFact {
    /// Parameter name as written.
    pub name: String,
    /// Whether the parameter carries a type annotation.
    pub annotated: bool,
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

impl DeclCollector<'_> {
    /// Records one declarator when it is a `const` identifier binding.
    /// Destructured patterns bind many symbols and are skipped.
    fn record_declarator(&mut self, declarator: &VariableDeclarator<'_>) {
        let BindingPattern::BindingIdentifier(binding) = &declarator.id else {
            return;
        };
        let name = slice_at(self.source, binding.span);
        let Some(name) = name else { return };
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
        self.functions.push(FunctionFact {
            symbol,
            scope: self.scopes.get(&symbol).copied().unwrap_or(u32::MAX),
            params,
            params_complex,
            return_annotation,
            body,
        });
    }
}

impl<'a> Visit<'a> for DeclCollector<'a> {
    fn visit_variable_declaration(&mut self, it: &VariableDeclaration<'a>) {
        if matches!(it.kind, VariableDeclarationKind::Const) {
            for declarator in &it.declarations {
                self.record_declarator(declarator);
            }
        }
        // Keep walking: initializers may nest functions/blocks that declare
        // their own consts (`const f = () => { const y = 1; … }`).
        walk::walk_variable_declaration(self, it);
    }

    fn visit_function(&mut self, it: &Function<'a>, flags: ScopeFlags) {
        self.record_function(it);
        // Keep walking: bodies nest consts and further function declarations
        // (`function o() { const y = 1; function i() { return y; } … }`).
        walk::walk_function(self, it, flags);
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

    let (decls, functions) = collect_decls(file, source, &parse.program, &symbols);
    ParsedFile {
        file,
        scopes,
        symbols,
        unresolved,
        imports,
        decls,
        functions,
        errors,
    }
}

/// Runs the targeted declarator walk and returns owned facts.
///
/// Symbol linkage resolves each declarator's `(name, binding start)` to the
/// per-file [`SymbolFact`] index built above; facts come out in source
/// (visitor) order, so the sequences are deterministic.
fn collect_decls<'a>(
    file: FileId,
    source: &'a str,
    program: &Program<'a>,
    symbols: &[SymbolFact],
) -> (Vec<DeclFact>, Vec<FunctionFact>) {
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
    };
    collector.visit_program(program);
    (collector.decls, collector.functions)
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
        let destructured = &pf.functions[1];
        assert!(destructured.params_complex);
        assert!(destructured.params.is_empty());
    }
}
