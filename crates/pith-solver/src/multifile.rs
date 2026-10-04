//! Multi-file programs (P019): import graphs, cross-file checking, and
//! cross-file invalidation.
//!
//! Pipeline per program: drivers adapt each file's frontend facts into
//! [`ProgramFile`] inputs (declaration names, scopes, spans, annotation
//! texts, and literal kinds verbatim from facts) plus a [`ModuleGraph`]
//! adapted from the module facts, then [`check_program`] checks every file
//! with imports resolved and returns one [`ProgramReport`] sorted by
//! [`FileId`].
//!
//! Probe basis (tsc 7.0.2 `--strict --pretty false`, `.agent/scratch/p019-probes/`):
//!
//! - Clean value/type/call imports check silently; a wrong-typed value use
//!   diagnoses `TS2322` at the use declarator, a wrong call argument
//!   `TS2345` at the argument — the same families and anchors as
//!   single-file checks.
//! - `import { NOPE } from "./shared"` diagnoses `TS2305` at the IMPORTED
//!   name (column-tested with aliases: `import { NOPE as N }` anchors at
//!   `NOPE`), one per binding, with no follow-on error at uses of the name.
//!   `import { A, B } from "./missing"` diagnoses ONE `TS2307` at the
//!   specifier per statement. The solver mirrors all three (codes
//!   [`CODE_NO_EXPORTED`]/[`CODE_NO_MODULE`]).
//! - Named re-export chains (`export { X } from`) and `export *` barrels
//!   resolve transitively (clean when the target is clean); `./sub`
//!   resolves to `sub/index.ts`; explicit `./shared.ts` suffixes are a
//!   `TS5097` in tsc without `allowImportingTsExtensions` (the graph resolves
//!   them leniently when the file exists — a pinned superset, see
//!   [`pith_symbols::multifile`]).
//! - Cross-file interface annotations check with the interface-name spelling
//!   (`TS2322` wrong member, `TS2741` missing — the P017 families intact).
//! - A type used as a value diagnoses `TS2693` in tsc; the solver declines
//!   those uses with reasons (pinned oracle-error divergence).
//! - Failed `import type` resolutions decline with reasons instead of
//!   `PITH2305`/`PITH2307`/`PITH2304` — a pinned divergence: a failing
//!   type-only resolution may name a member the target exports only as a
//!   type through shapes the subset cannot spell (chained or complex
//!   aliases), so diagnosing would risk false verdicts where tsc stays
//!   clean. Failed VALUE imports keep the exact mirrors (their export space
//!   is fully facted). Resolved type-only imports (including aliases the
//!   graph sees) stay silent like tsc and check through the shape paths.
//! - Re-exported interfaces and single-link aliases check with the same
//!   families and anchors through named chains, renames, and `export *`
//!   barrels (P035 probes, tsc 7.0.2, `.agent/scratch/p035-probes/`): wrong
//!   members diagnose `TS2322` at the member, missing members `TS2741`
//!   spelling the UNDERLYING interface (aliases expand transparently), and
//!   primitive aliases behave exactly like their target spelling.
//!   `export type` / `export { type X }` / `export type *` forms are
//!   identical to value forms. Ambiguous stars diagnose `TS2308` at the
//!   barrel statement and cycles `TS2303` at the re-export statements — both
//!   pinned gaps: the solver declines with reasons instead of guessing.
//!   Alias chains (`type B = A`, aliases over imports) resolve transitively
//!   up to the shared depth bound (P052 — the old single-level chained
//!   decline is gone); over-deep chains and cycles decline distinctly
//!   (e2e-pinned).
//!
//! - Missing/excess elaborations through an ALIAS spell the alias as written
//!   (`required in type 'Alias'`) where tsc spells the underlying interface
//!   (`'Point'`): the use-site spelling feeds the shared object path as the
//!   display text, and re-plumbing that display through [`check_enums`]
//!   would touch the shared single-file interface path. Pinned message
//!   divergence — the family, anchor, and structure all match, so no corpus
//!   fixture covers alias-missing (direct re-exported missing does).
//!
//! Driver seams (all disclosed, mirroring the narrowing/check-enums
//! precedents): identifier-initializer names ride [`ProgramFile::ident_inits`]
//! (sliced at the adapter's fact spans, bare identifiers only), enum literal
//! spellings ride [`ProgramFile::enum_texts`], and object-literal members
//! travel inside [`ConstDecl::init_object`] — the adapter emits no
//! expression facts, so drivers hand-feed exactly these three seams and
//! nothing else. [`ProgramFile::consts`] otherwise maps 1:1 from adapter
//! `DeclFact`s (unresolved inits stay [`InitKind::NonLiteral`]).
//!
//! Resolution rules (linkage is by `(FileId, name)` through the graph, never
//! by symbol identity across files — import bindings are distinct symbols
//! per file by design):
//!
//! - Local declarations shadow imports: an initializer or annotation naming
//!   a locally-declared const keeps single-file behavior (duplicate
//!   identifiers are future work — tsc's `TS2300` is the pinned gap).
//! - Value uses resolve to the declaring file's literal const inits (object
//!   inits clone through); the use-file memo entry records
//!   `Dep { declaring file, declaring occurrence }` alongside its self-dep,
//!   so editing the shared declaration invalidates exactly its dependents.
//!   Import failures need no use-site note (the import diagnostic or decline
//!   covers them — the unresolved-callee precedent); only genuine cross-file
//!   gaps (non-literal/ambiguous/kind-mismatched targets) note at the use.
//! - Annotations resolving to the declaring file's interfaces/enums relink
//!   onto the LOCAL import binding's symbol and check through [`check_enums`]
//!   unchanged; value targets there decline via the existing not-an-enum
//!   path (tsc's `TS2749` is the pinned gap). Annotations naming an imported
//!   alias expand transitively (P052) against the declaring file, following
//!   import hops across files: alias-to-primitive rewrites the annotation to
//!   the target spelling (checked exactly as if written); alias-to-interface
//!   and alias-to-enum relink the declaring shape onto the local import
//!   binding like a direct shape import.
//!   Over-deep, cyclic, generic, and non-identifier targets decline with
//!   reasons and skip checking (a raw check would add a second, misleading
//!   not-an-enum note). Annotations naming a type-only
//!   import the graph cannot resolve skip checking with a recorded reason
//!   (a failed type-only resolution may name a member exported only through
//!   shapes the subset cannot spell — `PITH2304` there would risk a false
//!   verdict).
//! - Calls merge imported function declarations (parameters from the
//!   declaring file) with local ones and check through [`check_calls`]
//!   unchanged — calls are unmemoized, so they record no query deps
//!   (consistent with single-file checking).
//! - Function returns over cross-file (or locally shaped) named types skip
//!   with reasons: the synthetic-const return path cannot spell them and
//!   must not invent `PITH2304`s. Returns over failed imports skip silently:
//!   the `PITH2305`/`PITH2307` diagnostic already covers them.
//!
//! [`InitKind::NonLiteral`]: super::InitKind

use std::collections::{HashMap, HashSet};

use pith_ids::{FileId, Span};
use pith_queries::{Dep, QueryDb};
use pith_symbols::{
    multifile::{ImportError, ImportedName, ModuleGraph, ResolvedExport},
    Binder,
};

use super::{
    check_calls, check_enums, check_functions, ArrayInit, CallSite, ConstDecl, EnumDecl, EnumInput,
    EnumShape, FileReport, FunctionDecl, InitKind, InterfaceShape, NamespaceShape, ObjectInit,
};

/// Code for missing exported members (oracle `TS2305`).
pub const CODE_NO_EXPORTED: &str = "PITH2305";
/// Code for unresolvable modules (oracle `TS2307`).
pub const CODE_NO_MODULE: &str = "PITH2307";

/// One import binding for checking, driver-mapped from the frontend's
/// `NamedImportFact` (mechanical field copy).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportUse {
    /// Local name as written.
    pub local: String,
    /// Requested name in the target module.
    pub imported: ImportedName,
    /// Module specifier as written.
    pub specifier: String,
    /// Owning scope of the local binding (for shape relinking).
    pub scope: u32,
    /// Span of the local binding name.
    pub span: Span,
    /// Span of the imported name, when one exists (anchors `PITH2305`).
    pub imported_span: Option<Span>,
    /// Span of the module-specifier string (anchors `PITH2307`).
    pub specifier_span: Span,
    /// `true` for `import type` bindings (mechanical copy of the frontend
    /// flag: elision is unobservable to checking). Failed type-only imports
    /// decline with reasons instead of diagnosing — the subset facts no
    /// type-alias space, so a failing type-only resolution may name a member
    /// the target does export as a type, and `PITH2305`/`PITH2307` there
    /// would risk a false verdict where tsc stays clean.
    pub is_type: bool,
}

/// One imported type alias, driver-mapped from the frontend's
/// `TypeAliasFact` (mechanical name + target-text copy).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasShape {
    /// Alias name as written in the declaring file.
    pub name: String,
    /// Verbatim aliased-type text (`"Point"`, `"number"`).
    pub target: String,
    /// `true` when the alias declares type parameters: expansion declines
    /// instead of instantiating it.
    pub has_type_params: bool,
}

/// One file's checking inputs for [`check_program`].
///
/// Declaration fields map 1:1 from adapter facts (see the module-level seam
/// notes); only `ident_inits`/`enum_texts` are driver-sliced and only
/// `consts` inits for imported names are driver-resolved — every other
/// resolution happens inside [`check_program`] through the graph.
#[derive(Clone, Debug)]
pub struct ProgramFile {
    /// File identity.
    pub file: FileId,
    /// Const/let declarators in source order (unresolved inits stay
    /// [`InitKind::NonLiteral`]).
    pub consts: Vec<ConstDecl>,
    /// Sliced initializer identifier per declarator, parallel to `consts`
    /// (`None` for literal/missing/complex inits — the disclosed use seam).
    pub ident_inits: Vec<Option<String>>,
    /// Sliced initializer text per declarator, parallel to `consts` (the
    /// [`EnumDecl`] seam; `None` where that path never reads it).
    pub enum_texts: Vec<Option<String>>,
    /// Local function declarations in source order.
    pub functions: Vec<FunctionDecl>,
    /// Local direct call sites in source order.
    pub calls: Vec<CallSite>,
    /// Local interface shapes in source order.
    pub interfaces: Vec<InterfaceShape>,
    /// Local enum shapes in source order.
    pub enums: Vec<EnumShape>,
    /// Local namespace shapes in source order.
    pub namespaces: Vec<NamespaceShape>,
    /// Local type aliases in source order (feeds transitive expansion of
    /// imported annotations; see [`AliasShape`]).
    pub aliases: Vec<AliasShape>,
    /// Local import bindings in source order.
    pub imports: Vec<ImportUse>,
}

/// One program's verdict: per-file reports sorted by [`FileId`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProgramReport {
    /// `(file, report)` pairs in [`FileId`] order; each report is sorted by
    /// `(file, span.lo, span.hi)` like every single-file entry point.
    pub files: Vec<(FileId, FileReport)>,
}

impl ProgramReport {
    /// The report for `file`, if checked.
    #[must_use]
    pub fn file(&self, file: FileId) -> Option<&FileReport> {
        self.files
            .iter()
            .find(|(checked, _)| *checked == file)
            .map(|(_, report)| report)
    }

    /// Total diagnostics across all files.
    #[must_use]
    pub fn diagnostic_count(&self) -> usize {
        self.files
            .iter()
            .map(|(_, report)| report.diagnostics.len())
            .sum()
    }

    /// Total unsupported notes across all files.
    #[must_use]
    pub fn unsupported_count(&self) -> usize {
        self.files
            .iter()
            .map(|(_, report)| report.unsupported.len())
            .sum()
    }
}

/// Whether `text` is a bare identifier (the routing rule for cross-file
/// names — mirrors the narrowing driver's disclosed slice check).
fn is_bare_identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// Mutable checking state for one [`check_program`] file, bundled so the
/// per-decl helpers stay lean (pedantic arity discipline).
struct FileCtx<'a> {
    input: &'a ProgramFile,
    graph: &'a ModuleGraph,
    by_file: &'a HashMap<FileId, usize>,
    files: &'a [ProgramFile],
    binder: &'a Binder,
    db: &'a mut QueryDb,
    report: FileReport,
}

/// The declaring file's inputs for a resolved export, if the driver passed
/// them (`None` is driver skew — callers decline, never assume).
fn declaring_input<'a>(
    files: &'a [ProgramFile],
    by_file: &HashMap<FileId, usize>,
    resolved: &ResolvedExport,
) -> Option<&'a ProgramFile> {
    by_file
        .get(&resolved.file)
        .and_then(|index| files.get(*index))
}

/// Checks every file in `files` with imports resolved through `graph`,
/// threading all declarations through `db` (one shared memo store — the
/// persistent thesis) and returning the sorted [`ProgramReport`].
///
/// Files check in input order against one [`Binder`] holding every file's
/// scope tree; output sorts by [`FileId`], so repeated runs agree
/// byte-for-byte whatever order drivers pass.
#[must_use]
pub fn check_program(
    files: &[ProgramFile],
    graph: &ModuleGraph,
    binder: &Binder,
    db: &mut QueryDb,
) -> ProgramReport {
    let by_file: HashMap<FileId, usize> = files
        .iter()
        .enumerate()
        .map(|(index, input)| (input.file, index))
        .collect();
    let mut out = ProgramReport::default();
    for input in files {
        let mut ctx = FileCtx {
            input,
            graph,
            by_file: &by_file,
            files,
            binder,
            db: &mut *db,
            report: FileReport::default(),
        };
        check_import_statements(&mut ctx);
        check_const_decls(&mut ctx);
        check_function_decls(&mut ctx);
        check_call_sites(&mut ctx);
        super::sort_report(&mut ctx.report);
        out.files.push((input.file, ctx.report));
    }
    out.files.sort_by_key(|(file, _)| *file);
    out
}

/// Emits `PITH2305`/`PITH2307` for unresolvable import bindings.
///
/// Unresolvable specifiers diagnose once per specifier (one oracle `TS2307`
/// per statement even with several bindings — probed); missing members
/// diagnose once per binding at the imported-name span (one oracle `TS2305`
/// per binding — probed); other failures decline with reasons.
///
/// Type-only imports never diagnose (any failure shape declines): their
/// export space includes type aliases the subset never facts, so a
/// diagnostic would risk a false verdict where tsc stays clean (probed:
/// `import type` of an existing alias is silent). Value imports keep the
/// exact mirrors — their export space is fully facted.
fn check_import_statements(ctx: &mut FileCtx<'_>) {
    let file = ctx.input.file;
    let mut reported: HashSet<String> = HashSet::new();
    for use_ in &ctx.input.imports {
        match ctx.graph.resolve_import(file, &use_.local) {
            Ok(_) => {}
            Err(other) if use_.is_type => {
                ctx.report.unsupported.push(super::UnsupportedDecl {
                    file,
                    span: use_.span,
                    reason: format!(
                        "type-only import '{}' from '{}': {}: \
                         type aliases are outside the subset",
                        use_.local,
                        use_.specifier,
                        other.reason()
                    ),
                });
            }
            Err(ImportError::UnresolvableSpecifier { specifier, .. }) => {
                if reported.insert(specifier.clone()) {
                    ctx.report.diagnostics.push(super::PithDiagnostic {
                        code: CODE_NO_MODULE.to_owned(),
                        file,
                        span: use_.specifier_span,
                        message: format!(
                            "Cannot find module '{specifier}' \
                             or its corresponding type declarations."
                        ),
                    });
                }
            }
            Err(ImportError::NotExported { name, .. }) => {
                ctx.report.diagnostics.push(super::PithDiagnostic {
                    code: CODE_NO_EXPORTED.to_owned(),
                    file,
                    span: use_.imported_span.unwrap_or(use_.span),
                    message: format!(
                        "Module '\"{}\"' has no exported member '{name}'.",
                        use_.specifier
                    ),
                });
            }
            Err(other) => {
                ctx.report.unsupported.push(super::UnsupportedDecl {
                    file,
                    span: use_.span,
                    reason: format!(
                        "import '{}' from '{}': {}",
                        use_.local,
                        use_.specifier,
                        other.reason()
                    ),
                });
            }
        }
    }
}

/// Whether a local const declarator bears `name` (locals shadow imports).
fn has_local_const(input: &ProgramFile, name: &str) -> bool {
    input.consts.iter().any(|decl| decl.name == name)
}

/// Whether `annotation` resolves locally to an interface, enum, or
/// namespace shape (those shadow any same-name import).
fn has_local_shape(ctx: &FileCtx<'_>, scope: u32, annotation: &str) -> bool {
    ctx.binder
        .resolve(ctx.input.file, scope, annotation)
        .is_some_and(|id| {
            ctx.input
                .interfaces
                .iter()
                .any(|shape| shape.symbol == Some(id))
                || ctx.input.enums.iter().any(|shape| shape.symbol == Some(id))
                || ctx
                    .input
                    .namespaces
                    .iter()
                    .any(|shape| shape.symbol == Some(id))
        })
}

/// A resolved cross-file value: the declaring init plus the [`Dep`] edge the
/// use-file memo entry records alongside its self-dep.
struct ResolvedInit {
    /// Declaring initializer kind (`None` for missing initializers, which
    /// check as "missing initializer" with the edge still recorded).
    init: Option<InitKind>,
    /// Declaring object members, when the initializer is `{ ... }`.
    init_object: Option<ObjectInit>,
    /// Declaring array members, when the initializer is `[ ... ]`.
    init_array: Option<ArrayInit>,
    /// The declaring occurrence this use depends on.
    dep: Dep,
}

/// Resolves one identifier initializer through the import graph.
///
/// `None` means single-file behavior applies: unimported names keep their
/// [`InitKind::NonLiteral`] verdict path, and import failures fall through
/// the same way (the import diagnostic or decline already covers them).
/// `Some(Err)` carries only genuine cross-file gaps (non-literal,
/// ambiguous, or kind-mismatched targets).
fn resolve_value_init(ctx: &FileCtx<'_>, target: &str) -> Option<Result<ResolvedInit, String>> {
    if !ctx.input.imports.iter().any(|entry| entry.local == target) {
        return None;
    }
    let Ok(resolved) = ctx.graph.resolve_import(ctx.input.file, target) else {
        return None;
    };
    let Some(declaring) = declaring_input(ctx.files, ctx.by_file, &resolved) else {
        return Some(Err(format!(
            "declaring file for import '{target}' has no inputs: driver skew"
        )));
    };
    let matches: Vec<(usize, &ConstDecl)> = declaring
        .consts
        .iter()
        .enumerate()
        .filter(|(_, decl)| decl.name == resolved.local)
        .collect();
    if matches.len() != 1 {
        return Some(Err(non_const_target(declaring, &resolved)));
    }
    let (index, found) = matches[0];
    if found.init == Some(InitKind::NonLiteral) {
        return Some(Err(format!(
            "imported '{}' has a non-literal initializer: outside the subset",
            resolved.local
        )));
    }
    Some(Ok(ResolvedInit {
        init: found.init,
        init_object: found.init_object.clone(),
        init_array: found.init_array.clone(),
        dep: Dep {
            file: resolved.file,
            node: super::occurrence_node(index),
        },
    }))
}

/// Explains why a resolved import target contributes no const value: a
/// function or type there (pinned `TS2693`-family divergences), several
/// same-name declarations, or nothing declarative at all (driver skew or an
/// out-of-subset declaration such as a class).
fn non_const_target(declaring: &ProgramFile, resolved: &ResolvedExport) -> String {
    let name = resolved.local.as_str();
    if declaring.functions.iter().any(|decl| decl.name == name) {
        return format!(
            "imported '{name}' is a function, used as a value: \
             function types are outside the subset"
        );
    }
    if declaring.interfaces.iter().any(|shape| shape.name == name)
        || declaring.enums.iter().any(|shape| shape.name == name)
    {
        return format!(
            "imported '{name}' is a type, used as a value: \
             value uses of types are outside the subset"
        );
    }
    format!("declaring file has no value declaration for '{name}': outside the subset")
}

/// Relinks a declaring file's interface/enum shape onto the local import
/// binding so [`check_enums`] resolves it through the checking [`Binder`].
fn relinked_symbol(ctx: &FileCtx<'_>, target: &str) -> Option<pith_ids::SymbolId> {
    let scope = ctx
        .input
        .imports
        .iter()
        .find(|entry| entry.local == target)
        .map(|entry| entry.scope)?;
    ctx.binder.resolve(ctx.input.file, scope, target)
}

/// A declaring file's shape relinked onto the use file's import binding.
#[derive(Clone, Debug)]
enum ShapeHit {
    /// An interface shape with `symbol` relinked locally.
    Interface(InterfaceShape),
    /// An enum shape with `symbol` relinked locally.
    Enum(EnumShape),
}

/// Finds one declaring file's shape by name, relinked onto the use file's
/// import binding symbol: interfaces before enums (merged pairs are illegal
/// in tsc). `None` means no shape claims the name (values, type aliases,
/// classes); `Some(Err)` carries only the multiple-declaration gaps.
fn declaring_shape(
    declaring: &ProgramFile,
    name: &str,
    symbol: Option<pith_ids::SymbolId>,
) -> Option<Result<ShapeHit, String>> {
    if declaring
        .interfaces
        .iter()
        .filter(|shape| shape.name == name)
        .count()
        > 1
    {
        return Some(Err(format!(
            "multiple interface declarations for '{name}': merging is outside the subset"
        )));
    }
    if let Some(shape) = declaring.interfaces.iter().find(|shape| shape.name == name) {
        let mut relinked = shape.clone();
        relinked.symbol = symbol;
        return Some(Ok(ShapeHit::Interface(relinked)));
    }
    if declaring
        .enums
        .iter()
        .filter(|shape| shape.name == name)
        .count()
        > 1
    {
        return Some(Err(format!(
            "multiple enum declarations for '{name}': merging is outside the subset"
        )));
    }
    if let Some(shape) = declaring.enums.iter().find(|shape| shape.name == name) {
        let mut relinked = shape.clone();
        relinked.symbol = symbol;
        return Some(Ok(ShapeHit::Enum(relinked)));
    }
    None
}

/// Resolves one annotation name through the import graph to a declaring
/// file's shape: interfaces before enums (merged pairs are illegal in tsc).
/// `None` means local handling applies (unimported names and import
/// failures, whose records already exist); `Some(Err)` carries only the
/// multiple-declaration gaps.
fn resolve_type_shape(ctx: &FileCtx<'_>, target: &str) -> Option<Result<ShapeHit, String>> {
    if !ctx.input.imports.iter().any(|entry| entry.local == target) {
        return None;
    }
    let Ok(resolved) = ctx.graph.resolve_import(ctx.input.file, target) else {
        return None;
    };
    let Some(declaring) = declaring_input(ctx.files, ctx.by_file, &resolved) else {
        return Some(Err(format!(
            "declaring file for import '{target}' has no inputs: driver skew"
        )));
    };
    declaring_shape(declaring, &resolved.local, relinked_symbol(ctx, target))
}

/// One alias expansion step for an imported annotation.
enum AliasStep {
    /// Alias-to-primitive: the annotation rewrites to the target spelling
    /// and checks exactly as if written.
    Primitive(String),
    /// Alias-to-interface/enum: the declaring shape, relinked locally.
    Shape(ShapeHit),
    /// Unexpandable: over-deep, cyclic, generic, or complex targets decline.
    Decline(String),
}

/// Terminal outcome of following one imported alias chain (P052): either
/// a primitive spelling, a declaring file's shape claim, or a decline
/// reason.
enum ChainTerminal {
    /// Alias chain ends at a primitive/boundary: the annotation rewrites to
    /// this spelling and checks exactly as if written.
    Primitive(String),
    /// Alias chain ends at an interface/enum in this declaring file: the
    /// shape, relinked onto the use-file import binding by the caller.
    Shape(ShapeHit),
    /// Unexpandable: over-deep, cyclic, generic, complex, or unclaimed links
    /// decline with distinct reasons.
    Decline(String),
}

/// Walking state for [`follow_import_chain`], bundled so the link step stays
/// lean (pedantic arity discipline).
struct ImportChain<'c, 'x> {
    /// The checking file context (graph, files, binder for relinking).
    ctx: &'c FileCtx<'x>,
    /// `(file, name)` pairs followed so far (head first): the cycle guard.
    visited: Vec<(FileId, String)>,
    /// Head alias name in the head declaring file (names head-attributed
    /// reasons: over-depth limits and unclaimed terminals).
    head: String,
    /// Links followed so far (alias advances and import hops alike count
    /// one, against the shared [`super::MAX_ALIAS_CHAIN_DEPTH`]).
    links: usize,
}

/// One [`ImportChain`] link outcome: terminal outcomes return to the caller
/// while advances hand owned handoffs back to the loop.
enum ImportLink<'x> {
    /// Terminal: map to the [`AliasStep`].
    Done(ChainTerminal),
    /// Advance within the same declaring file: the next alias's target text
    /// (the next linker is the name just classified).
    Within(String),
    /// Hop through an import to another declaring file: the file plus the
    /// resolved name (settled by [`ImportChain::hop`] — the loop never
    /// classifies a bare resolved name as target text, which would falsely
    /// trip the self-cycle check).
    Hop(&'x ProgramFile, String),
}

/// One [`ImportChain::hop`] settlement: either loop handoffs (file, linker
/// name, target text) or a terminal outcome.
enum HopSettled<'x> {
    /// Keep walking: the declaring file, the alias name, its target text.
    Continue(&'x ProgramFile, String, String),
    /// Terminal: map to the [`AliasStep`].
    Done(ChainTerminal),
}

impl<'x> ImportChain<'_, 'x> {
    /// Classifies one link (`target` is the trimmed target text of the alias
    /// named `linker` in `file`): primitives rewrite, shapes in the
    /// declaring file terminate, and live alias/import links advance the
    /// walk when the bound allows — anything else declines distinctly.
    fn link(&mut self, file: &ProgramFile, linker: &str, target: &str) -> ImportLink<'x> {
        if target.is_empty() || target == linker {
            return ImportLink::Done(ChainTerminal::Decline(format!(
                "type alias '{linker}' is circular: circular aliases are outside the subset"
            )));
        }
        if visited_contains(&self.visited, file.file, target) {
            return ImportLink::Done(ChainTerminal::Decline(format!(
                "type alias '{linker}' targets '{target}': \
                 circular alias chains are outside the subset"
            )));
        }
        if super::annotation_type(target).is_some()
            || super::boundary_annotation_type(target).is_some()
        {
            return ImportLink::Done(ChainTerminal::Primitive(target.to_owned()));
        }
        if !is_bare_identifier(target) {
            return ImportLink::Done(ChainTerminal::Decline(format!(
                "type alias '{linker}' targets '{target}': \
                 non-identifier alias targets are outside the subset"
            )));
        }
        if let Some(hit) = declaring_shape(file, target, None) {
            return ImportLink::Done(match hit {
                Ok(shape) => ChainTerminal::Shape(shape),
                Err(reason) => ChainTerminal::Decline(reason),
            });
        }
        let mut claimed = file.aliases.iter().filter(|shape| shape.name == target);
        if let Some(next) = claimed.next() {
            if claimed.next().is_some() {
                return ImportLink::Done(ChainTerminal::Decline(format!(
                    "multiple type alias declarations for '{target}': \
                     merging is outside the subset"
                )));
            }
            if next.has_type_params {
                return ImportLink::Done(ChainTerminal::Decline(format!(
                    "type alias '{}' is generic: generic aliases are outside the subset",
                    next.name
                )));
            }
            self.links += 1;
            if self.links > super::MAX_ALIAS_CHAIN_DEPTH {
                return ImportLink::Done(over_depth(&self.head, target));
            }
            self.visited.push((file.file, target.to_owned()));
            return ImportLink::Within(next.target.clone());
        }
        if file.imports.iter().any(|entry| entry.local == target) {
            match self.ctx.graph.resolve_import(file.file, target) {
                Err(other) => {
                    return ImportLink::Done(ChainTerminal::Decline(format!(
                        "type alias '{linker}' targets imported '{target}': {}",
                        other.reason()
                    )));
                }
                Ok(resolved) => {
                    let Some(next_file) =
                        declaring_input(self.ctx.files, self.ctx.by_file, &resolved)
                    else {
                        return ImportLink::Done(ChainTerminal::Decline(format!(
                            "declaring file for import '{target}' has no inputs: driver skew"
                        )));
                    };
                    if visited_contains(&self.visited, next_file.file, &resolved.local) {
                        return ImportLink::Done(ChainTerminal::Decline(format!(
                            "type alias '{linker}' targets '{target}': \
                             circular alias chains are outside the subset"
                        )));
                    }
                    self.links += 1;
                    if self.links > super::MAX_ALIAS_CHAIN_DEPTH {
                        return ImportLink::Done(over_depth(&self.head, target));
                    }
                    self.visited.push((next_file.file, resolved.local.clone()));
                    return ImportLink::Hop(next_file, resolved.local);
                }
            }
        }
        ImportLink::Done(ChainTerminal::Decline(format!(
            "type alias '{}' targets '{target}': \
             no interface, enum, or primitive claims it",
            self.head
        )))
    }

    /// Settles an import hop to (`next_file`, `next_name`): aliases continue
    /// the walk with their own target text, shapes terminate, and anything
    /// else declines — the loop never classifies the bare resolved name as
    /// target text (which would falsely trip the self-cycle check).
    fn hop(&mut self, next_file: &'x ProgramFile, next_name: &str) -> HopSettled<'x> {
        let mut claimed = next_file
            .aliases
            .iter()
            .filter(|shape| shape.name == next_name);
        let Some(next) = claimed.next() else {
            return match declaring_shape(next_file, next_name, None) {
                Some(Ok(shape)) => HopSettled::Done(ChainTerminal::Shape(shape)),
                Some(Err(reason)) => HopSettled::Done(ChainTerminal::Decline(reason)),
                None => HopSettled::Done(ChainTerminal::Decline(format!(
                    "type alias '{}' targets '{next_name}': \
                     no interface, enum, or primitive claims it",
                    self.head
                ))),
            };
        };
        if claimed.next().is_some() {
            return HopSettled::Done(ChainTerminal::Decline(format!(
                "multiple type alias declarations for '{next_name}': \
                 merging is outside the subset"
            )));
        }
        if next.has_type_params {
            return HopSettled::Done(ChainTerminal::Decline(format!(
                "type alias '{}' is generic: generic aliases are outside the subset",
                next.name
            )));
        }
        HopSettled::Continue(next_file, next.name.clone(), next.target.trim().to_owned())
    }
}

/// Whether (`file`, `name`) is already in the walk's visited set: the cycle
/// guard shared by the link and hop steps (each alias names at most one
/// target, so a revisit is exactly a cycle).
fn visited_contains(visited: &[(FileId, String)], file: FileId, name: &str) -> bool {
    visited
        .iter()
        .any(|(visited_file, candidate)| *visited_file == file && candidate == name)
}

/// The over-depth decline: names the head alias (stable whatever link trips
/// the bound) plus the link target that exceeded it.
fn over_depth(head: &str, target: &str) -> ChainTerminal {
    ChainTerminal::Decline(format!(
        "type alias '{head}' targets '{target}': \
         alias chain is deeper than {} links: \
         deep alias chains are outside the subset",
        super::MAX_ALIAS_CHAIN_DEPTH
    ))
}

/// Follows one imported alias chain to its terminal target, threading the
/// visited set and the shared depth bound across declaring files (import
/// hops continue the walk — tsc resolves those too).
fn follow_import_chain(
    ctx: &FileCtx<'_>,
    declaring: &ProgramFile,
    alias: &AliasShape,
) -> ChainTerminal {
    if alias.has_type_params {
        return ChainTerminal::Decline(format!(
            "type alias '{}' is generic: generic aliases are outside the subset",
            alias.name
        ));
    }
    let mut chain = ImportChain {
        ctx,
        visited: vec![(declaring.file, alias.name.clone())],
        head: alias.name.clone(),
        links: 0,
    };
    let mut file = declaring;
    let mut linker = alias.name.clone();
    let mut target = alias.target.trim().to_owned();
    loop {
        match chain.link(file, &linker, &target) {
            ImportLink::Done(outcome) => return outcome,
            ImportLink::Within(next_target) => {
                linker.clone_from(&target);
                next_target.trim().clone_into(&mut target);
            }
            ImportLink::Hop(next_file, next_name) => match chain.hop(next_file, &next_name) {
                HopSettled::Continue(hopped_file, hopped_linker, hopped_target) => {
                    file = hopped_file;
                    linker = hopped_linker;
                    target = hopped_target;
                }
                HopSettled::Done(outcome) => return outcome,
            },
        }
    }
}

/// Expands one imported annotation naming a declaring-file alias,
/// transitively up to the shared depth bound (P052).
///
/// `None` means no expansion applies: unimported names, import failures
/// (whose records already exist), and names no declaring alias claims (the
/// existing unknown-name path applies). Primitives rewrite to their
/// spelling; interfaces and enums relink like direct shape imports; the walk
/// follows alias links within the declaring file and import hops across
/// files (tsc resolves those too), while over-deep chains, cycles (via the
/// visited set), generic aliases, and non-identifier targets decline —
/// never a forced verdict.
fn expand_imported_alias(ctx: &FileCtx<'_>, target: &str) -> Option<AliasStep> {
    if !ctx.input.imports.iter().any(|entry| entry.local == target) {
        return None;
    }
    let Ok(resolved) = ctx.graph.resolve_import(ctx.input.file, target) else {
        return None;
    };
    let declaring = declaring_input(ctx.files, ctx.by_file, &resolved)?;
    let alias = declaring
        .aliases
        .iter()
        .find(|shape| shape.name == resolved.local)?;
    Some(match follow_import_chain(ctx, declaring, alias) {
        ChainTerminal::Primitive(spelling) => AliasStep::Primitive(spelling),
        ChainTerminal::Shape(hit) => AliasStep::Shape(relinked_hit(ctx, target, hit)),
        ChainTerminal::Decline(reason) => AliasStep::Decline(reason),
    })
}

/// Relinks a chain-terminal shape onto the use file's import binding symbol
/// (the declaring-file lookup ran with no symbol; identity always comes from
/// the checking [`Binder`)).
fn relinked_hit(ctx: &FileCtx<'_>, target: &str, hit: ShapeHit) -> ShapeHit {
    let symbol = relinked_symbol(ctx, target);
    match hit {
        ShapeHit::Interface(mut shape) => {
            shape.symbol = symbol;
            ShapeHit::Interface(shape)
        }
        ShapeHit::Enum(mut shape) => {
            shape.symbol = symbol;
            ShapeHit::Enum(shape)
        }
    }
}

/// The decline reason when `target` is a type-only import whose resolution
/// fails: `None` for value imports and for anything that resolves (failed
/// value imports keep their `PITH2305`/`PITH2307` diagnostics; resolved
/// imports relink shapes through [`resolve_type_shape`]).
fn failed_type_import(ctx: &FileCtx<'_>, target: &str) -> Option<String> {
    if !ctx
        .input
        .imports
        .iter()
        .any(|entry| entry.local == target && entry.is_type)
    {
        return None;
    }
    match ctx.graph.resolve_import(ctx.input.file, target) {
        Ok(_) => None,
        Err(other) => Some(other.reason()),
    }
}

/// Declaration span for a use-file const declarator: the exact symbol id,
/// declarator scope, then caller fallback (the same contract as the
/// single-file span helper).
fn use_decl_span(ctx: &FileCtx<'_>, decl: &ConstDecl) -> Span {
    super::binder_span_for(
        ctx.binder,
        ctx.input.file,
        decl.name.as_str(),
        decl.scope,
        decl.symbol,
        decl.span,
    )
}

/// Queued checking state for one file's const declarators, bundled so the
/// annotation arms stay lean (pedantic arity discipline).
struct DeclSink {
    /// Declarations queued for [`check_enums`], parallel to `skip`.
    decls: Vec<EnumDecl>,
    /// Positions in `decls` whose declaration already declined: they skip
    /// `check_enums` instead of checking unannotated, which would add a
    /// second, misleading note for a declaration that does bear one.
    skip: Vec<bool>,
    /// Recorded decline reasons, drained into the report after checking.
    notes: Vec<(Span, String)>,
}

impl DeclSink {
    /// Queues one declaration, checked (`skipped: false`) or past checking.
    fn push(&mut self, decl: EnumDecl, skipped: bool) {
        self.decls.push(decl);
        self.skip.push(skipped);
    }

    /// Records one annotation decline and queues its already-resolved
    /// declaration past `check_enums` (checking the raw name would add a
    /// second, misleading note for a position that already declined).
    fn decline(
        &mut self,
        span: Span,
        reason: String,
        resolved: ConstDecl,
        init_text: Option<String>,
        deps: Vec<Dep>,
    ) {
        self.notes.push((span, reason));
        self.push(
            EnumDecl {
                decl: resolved,
                init_text,
                cross_file_deps: deps,
            },
            true,
        );
    }
}

/// Checks every const declarator: value inits resolve through imports (with
/// cross-file [`Dep`] edges), annotations relink imported shapes, then one
/// [`check_enums`] run verdicts the file.
/// Mutable checking state for one alias-expansion step, bundled so the
/// arity stays flat.
struct AliasStepCtx<'a> {
    index: usize,
    interfaces: &'a mut Vec<InterfaceShape>,
    enums: &'a mut Vec<EnumShape>,
    sink: &'a mut DeclSink,
}

/// Transitive alias expansion for one imported annotation (see
/// `expand_imported_alias`): primitives rewrite the annotation spelling,
/// interfaces/enums relink through the existing shape paths, and
/// unexpandable targets decline and skip checking like failed type-only
/// imports. Returns the (possibly rewritten) declaration plus deps, or
/// `None` when a decline was recorded and the caller should `continue`.
fn expand_alias_annotation(
    ctx: &FileCtx<'_>,
    annotation: &str,
    resolved: ConstDecl,
    deps: Vec<Dep>,
    step: AliasStepCtx<'_>,
) -> Option<(ConstDecl, Vec<Dep>)> {
    let AliasStepCtx {
        index,
        interfaces,
        enums,
        sink,
    } = step;
    match expand_imported_alias(ctx, annotation) {
        None => Some((resolved, deps)),
        Some(AliasStep::Primitive(spelling)) => {
            let mut resolved = resolved;
            resolved.annotation = Some(spelling);
            Some((resolved, deps))
        }
        Some(AliasStep::Shape(ShapeHit::Interface(shape))) => {
            interfaces.push(shape);
            Some((resolved, deps))
        }
        Some(AliasStep::Shape(ShapeHit::Enum(shape))) => {
            enums.push(shape);
            Some((resolved, deps))
        }
        Some(AliasStep::Decline(reason)) => {
            let span = use_decl_span(ctx, &resolved);
            let init_text = ctx.input.enum_texts.get(index).cloned().flatten();
            sink.decline(span, reason, resolved, init_text, deps);
            None
        }
    }
}

/// Resolves one declaration's identifier initializer through the
/// cross-file value graph for [`check_const_decls`]: resolved inits
/// (kinds, objects, arrays) substitute with a [`Dep`] edge; failures
/// record a note; local consts and missing entries pass through silently.
/// Mutates `resolved`/`deps` in place, notes into the sink.
fn resolve_const_value_init(
    ctx: &FileCtx<'_>,
    index: usize,
    resolved: &mut ConstDecl,
    deps: &mut Vec<Dep>,
    sink: &mut DeclSink,
) {
    let Some(target) = ctx
        .input
        .ident_inits
        .get(index)
        .and_then(|slot| slot.as_ref())
    else {
        return;
    };
    if has_local_const(ctx.input, target.as_str()) {
        return;
    }
    match resolve_value_init(ctx, target.as_str()) {
        None => {}
        Some(Ok(hit)) => {
            resolved.init = hit.init;
            resolved.init_object = hit.init_object;
            resolved.init_array = hit.init_array;
            deps.push(hit.dep);
        }
        Some(Err(reason)) => {
            sink.notes.push((use_decl_span(ctx, resolved), reason));
        }
    }
}

fn check_const_decls(ctx: &mut FileCtx<'_>) {
    let file = ctx.input.file;
    let mut sink = DeclSink {
        decls: Vec::with_capacity(ctx.input.consts.len()),
        skip: Vec::with_capacity(ctx.input.consts.len()),
        notes: Vec::new(),
    };
    let mut interfaces: Vec<InterfaceShape> = ctx.input.interfaces.clone();
    let mut enums: Vec<EnumShape> = ctx.input.enums.clone();
    for (index, decl) in ctx.input.consts.iter().enumerate() {
        let mut resolved = decl.clone();
        let mut deps: Vec<Dep> = Vec::new();
        resolve_const_value_init(ctx, index, &mut resolved, &mut deps, &mut sink);
        if let Some(raw) = resolved.annotation.as_deref().map(str::trim) {
            // Owned so the declaration below can move into the sink or the
            // alias step while the text is still in use.
            let annotation = raw.to_owned();
            if is_bare_identifier(&annotation)
                && super::annotation_type(&annotation).is_none()
                && !has_local_const(ctx.input, &annotation)
                && !has_local_shape(ctx, resolved.scope, &annotation)
            {
                match resolve_type_shape(ctx, &annotation) {
                    None => {
                        if let Some(reason) = failed_type_import(ctx, &annotation) {
                            // A type-only import the graph cannot resolve:
                            // checking the annotation would invent `PITH2304`
                            // where tsc may resolve the member cleanly, so
                            // the declaration skips checking and the gap is
                            // recorded here.
                            let span = use_decl_span(ctx, &resolved);
                            let name = annotation.clone();
                            let init_text = ctx.input.enum_texts.get(index).cloned().flatten();
                            sink.decline(
                                span,
                                format!(
                                    "type-only import '{name}': {reason}: \
                                     type aliases are outside the subset"
                                ),
                                resolved,
                                init_text,
                                deps,
                            );
                            continue;
                        }
                        // Transitive alias expansion: an imported
                        // annotation naming a declaring-file alias rewrites
                        // (primitives) or relinks (interfaces/enums) through
                        // the existing paths; unexpandable targets decline
                        // and skip checking like failed type-only imports.
                        let Some((rewritten, returned)) = expand_alias_annotation(
                            ctx,
                            &annotation,
                            resolved,
                            deps,
                            AliasStepCtx {
                                index,
                                interfaces: &mut interfaces,
                                enums: &mut enums,
                                sink: &mut sink,
                            },
                        ) else {
                            continue;
                        };
                        resolved = rewritten;
                        deps = returned;
                    }
                    Some(Ok(ShapeHit::Interface(shape))) => interfaces.push(shape),
                    Some(Ok(ShapeHit::Enum(shape))) => enums.push(shape),
                    Some(Err(reason)) => {
                        sink.notes.push((use_decl_span(ctx, &resolved), reason));
                    }
                }
            }
        }
        let init_text = ctx.input.enum_texts.get(index).cloned().flatten();
        sink.push(
            EnumDecl {
                decl: resolved,
                init_text,
                cross_file_deps: deps,
            },
            false,
        );
    }
    let decls: Vec<EnumDecl> = sink
        .decls
        .into_iter()
        .zip(sink.skip)
        .filter_map(|(decl, skipped)| (!skipped).then_some(decl))
        .collect();
    let input = EnumInput {
        enums: &enums,
        interfaces: &interfaces,
        namespaces: &ctx.input.namespaces,
    };
    let mut report = check_enums(file, &decls, &input, ctx.binder, &mut *ctx.db);
    for (span, reason) in sink.notes {
        report
            .unsupported
            .push(super::UnsupportedDecl { file, span, reason });
    }
    super::sort_report(&mut report);
    append_report(ctx, report);
}

/// Whether a function return annotation needs the cross-file pre-gate, and
/// what it records: a bare non-primitive name that names an import or a
/// local shape cannot check through the synthetic-const return path.
/// `SkipSilent` needs no note (a failed import's diagnostic covers it).
enum ReturnGate {
    /// Check normally through [`check_functions`].
    Check,
    /// Skip silently (failed import already diagnosed).
    SkipSilent,
    /// Decline with a reason at the declaration span.
    Decline(String),
}

/// Whether a function return annotation needs the cross-file pre-gate, and
/// what it records: a bare non-primitive name that names an import or a
/// local shape cannot check through the synthetic-const return path.
/// `SkipSilent` needs no note (a failed import's diagnostic covers it).
fn gated_return(ctx: &FileCtx<'_>, decl: &FunctionDecl) -> ReturnGate {
    let Some(annotation) = decl.return_annotation.as_deref().map(str::trim) else {
        return ReturnGate::Check;
    };
    if annotation.is_empty()
        || annotation.starts_with('{')
        || annotation.contains('|')
        || super::annotation_type(annotation).is_some()
        || !is_bare_identifier(annotation)
    {
        return ReturnGate::Check;
    }
    let imported = ctx
        .input
        .imports
        .iter()
        .any(|entry| entry.local == annotation);
    if !imported && !has_local_shape(ctx, decl.scope, annotation) {
        return ReturnGate::Check;
    }
    if imported
        && ctx
            .graph
            .resolve_import(ctx.input.file, annotation)
            .is_err()
    {
        return ReturnGate::SkipSilent;
    }
    let whose = if imported { "cross-file" } else { "local" };
    ReturnGate::Decline(format!(
        "return annotation '{annotation}' names a {whose} type: \
         function returns over named types are outside the subset"
    ))
}

/// Checks local function returns through [`check_functions`], pre-gating
/// named-type returns (see [`gated_return`]).
fn check_function_decls(ctx: &mut FileCtx<'_>) {
    let file = ctx.input.file;
    let mut checkable: Vec<FunctionDecl> = Vec::with_capacity(ctx.input.functions.len());
    let mut notes: Vec<(Span, String)> = Vec::new();
    for decl in &ctx.input.functions {
        match gated_return(ctx, decl) {
            ReturnGate::Check => checkable.push(decl.clone()),
            ReturnGate::SkipSilent => {}
            ReturnGate::Decline(reason) => {
                let span = super::binder_span_for(
                    ctx.binder,
                    file,
                    decl.name.as_str(),
                    decl.scope,
                    decl.symbol,
                    decl.span,
                );
                notes.push((span, reason));
            }
        }
    }
    let mut report = check_functions(file, &checkable, ctx.binder, &mut *ctx.db);
    for (span, reason) in notes {
        report
            .unsupported
            .push(super::UnsupportedDecl { file, span, reason });
    }
    super::sort_report(&mut report);
    append_report(ctx, report);
}

/// Merges imported function declarations (parameters from the declaring
/// file) with local ones for call checking: local-plus-imported same-name
/// pairs stay merged so the existing multiple-declaration decline fires
/// (tsc's `TS2300` duplicate is the pinned gap); unresolvable callees fall
/// into the existing undeclared-name decline.
///
/// Overload caveat (P044): merged imports always carry a `Complex` body, so
/// a local `declare function` plus an imported same-name now resolves the
/// import as the implementation instead of declining — defensible (the
/// import IS the implementation), and every multi-body shape still declines.
fn merged_functions(ctx: &FileCtx<'_>) -> Vec<FunctionDecl> {
    let mut merged: Vec<FunctionDecl> = ctx.input.functions.clone();
    // One imported declaration per callee name per file: pushing per call
    // site would fabricate same-name duplicates and trip the
    // multiple-declaration decline on every repeat call. Local-plus-imported
    // same-name pairs still merge (the decline is intended there).
    let mut pushed: HashSet<&str> = HashSet::new();
    for call in &ctx.input.calls {
        let name = call.callee.as_str();
        if !ctx.input.imports.iter().any(|entry| entry.local == name) {
            continue;
        }
        if !pushed.insert(name) {
            continue;
        }
        let Ok(resolved) = ctx.graph.resolve_import(ctx.input.file, name) else {
            continue;
        };
        let Some(declaring) = declaring_input(ctx.files, ctx.by_file, &resolved) else {
            continue;
        };
        for found in declaring
            .functions
            .iter()
            .filter(|decl| decl.name == resolved.local)
        {
            merged.push(FunctionDecl {
                name: call.callee.clone(),
                span: found.span,
                scope: found.scope,
                symbol: None,
                params: found.params.clone(),
                params_complex: found.params_complex,
                is_async: found.is_async,
                has_type_params: found.has_type_params,
                return_annotation: found.return_annotation.clone(),
                body: super::FunctionBody::Complex,
            });
        }
    }
    merged
}

/// Checks call sites against merged local-plus-imported declarations.
fn check_call_sites(ctx: &mut FileCtx<'_>) {
    let file = ctx.input.file;
    let merged = merged_functions(ctx);
    let report = check_calls(file, &merged, &ctx.input.calls, ctx.binder);
    append_report(ctx, report);
}

/// Merges one checker report into the file's verdict.
fn append_report(ctx: &mut FileCtx<'_>, mut report: FileReport) {
    ctx.report.diagnostics.append(&mut report.diagnostics);
    ctx.report.unsupported.append(&mut report.unsupported);
}
