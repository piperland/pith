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
//! - `import type` of an existing alias is silent in tsc; the solver
//!   declines failed type-only imports (and their annotation uses) with
//!   reasons instead of `PITH2305`/`PITH2307`/`PITH2304` — a pinned
//!   divergence, since type aliases emit no facts and diagnosing would risk
//!   false verdicts. Failed VALUE imports keep the exact mirrors (their
//!   export space is fully facted).
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
//!   path (tsc's `TS2749` is the pinned gap). Annotations naming a
//!   type-only import the graph cannot resolve skip checking with a
//!   recorded reason (type aliases emit no facts — `PITH2304` there would
//!   be a false verdict).
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
    check_calls, check_enums, check_functions, CallSite, ConstDecl, EnumDecl, EnumInput, EnumShape,
    FileReport, FunctionDecl, InitKind, InterfaceShape, NamespaceShape, ObjectInit,
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
    let symbol = relinked_symbol(ctx, target);
    if declaring
        .interfaces
        .iter()
        .filter(|shape| shape.name == resolved.local)
        .count()
        > 1
    {
        return Some(Err(format!(
            "multiple interface declarations for '{}': merging is outside the subset",
            resolved.local
        )));
    }
    if let Some(shape) = declaring
        .interfaces
        .iter()
        .find(|shape| shape.name == resolved.local)
    {
        let mut relinked = shape.clone();
        relinked.symbol = symbol;
        return Some(Ok(ShapeHit::Interface(relinked)));
    }
    if declaring
        .enums
        .iter()
        .filter(|shape| shape.name == resolved.local)
        .count()
        > 1
    {
        return Some(Err(format!(
            "multiple enum declarations for '{}': merging is outside the subset",
            resolved.local
        )));
    }
    if let Some(shape) = declaring
        .enums
        .iter()
        .find(|shape| shape.name == resolved.local)
    {
        let mut relinked = shape.clone();
        relinked.symbol = symbol;
        return Some(Ok(ShapeHit::Enum(relinked)));
    }
    None
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

/// Checks every const declarator: value inits resolve through imports (with
/// cross-file [`Dep`] edges), annotations relink imported shapes, then one
/// [`check_enums`] run verdicts the file.
fn check_const_decls(ctx: &mut FileCtx<'_>) {
    let file = ctx.input.file;
    let mut decls: Vec<EnumDecl> = Vec::with_capacity(ctx.input.consts.len());
    let mut interfaces: Vec<InterfaceShape> = ctx.input.interfaces.clone();
    let mut enums: Vec<EnumShape> = ctx.input.enums.clone();
    let mut notes: Vec<(Span, String)> = Vec::new();
    // Positions in `decls` whose declaration already declined (a failed
    // type-only import records its gap here): they skip `check_enums`
    // instead of checking unannotated, which would add a second, misleading
    // "no annotation" note for a declaration that does have one.
    let mut skip: Vec<bool> = Vec::with_capacity(ctx.input.consts.len());
    for (index, decl) in ctx.input.consts.iter().enumerate() {
        let mut resolved = decl.clone();
        let mut deps: Vec<Dep> = Vec::new();
        if let Some(target) = ctx
            .input
            .ident_inits
            .get(index)
            .and_then(|slot| slot.as_ref())
        {
            if !has_local_const(ctx.input, target.as_str()) {
                match resolve_value_init(ctx, target.as_str()) {
                    None => {}
                    Some(Ok(hit)) => {
                        resolved.init = hit.init;
                        resolved.init_object = hit.init_object;
                        deps.push(hit.dep);
                    }
                    Some(Err(reason)) => {
                        notes.push((use_decl_span(ctx, &resolved), reason));
                    }
                }
            }
        }
        if let Some(annotation) = resolved.annotation.as_deref().map(str::trim) {
            if is_bare_identifier(annotation)
                && super::annotation_type(annotation).is_none()
                && !has_local_const(ctx.input, annotation)
                && !has_local_shape(ctx, resolved.scope, annotation)
            {
                match resolve_type_shape(ctx, annotation) {
                    None => {
                        if let Some(reason) = failed_type_import(ctx, annotation) {
                            // A type-only import the value graph cannot see
                            // (type aliases emit no facts): checking the
                            // annotation would invent `PITH2304` where tsc
                            // resolves the alias cleanly, so the declaration
                            // skips checking and the gap is recorded here.
                            let span = use_decl_span(ctx, &resolved);
                            let name = annotation.to_owned();
                            notes.push((
                                span,
                                format!(
                                    "type-only import '{name}': {reason}: \
                                     type aliases are outside the subset"
                                ),
                            ));
                            skip.push(true);
                            let init_text = ctx.input.enum_texts.get(index).cloned().flatten();
                            decls.push(EnumDecl {
                                decl: resolved,
                                init_text,
                                cross_file_deps: deps,
                            });
                            continue;
                        }
                    }
                    Some(Ok(ShapeHit::Interface(shape))) => interfaces.push(shape),
                    Some(Ok(ShapeHit::Enum(shape))) => enums.push(shape),
                    Some(Err(reason)) => {
                        notes.push((use_decl_span(ctx, &resolved), reason));
                    }
                }
            }
        }
        let init_text = ctx.input.enum_texts.get(index).cloned().flatten();
        decls.push(EnumDecl {
            decl: resolved,
            init_text,
            cross_file_deps: deps,
        });
        skip.push(false);
    }
    let decls: Vec<EnumDecl> = decls
        .into_iter()
        .zip(skip)
        .filter_map(|(decl, skipped)| (!skipped).then_some(decl))
        .collect();
    let input = EnumInput {
        enums: &enums,
        interfaces: &interfaces,
        namespaces: &ctx.input.namespaces,
    };
    let mut report = check_enums(file, &decls, &input, ctx.binder, &mut *ctx.db);
    for (span, reason) in notes {
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
