//! Real-file end-to-end driver (PITH-P027): the pinned defu graph.
//!
//! Pipeline mirrors `e2e_check_multifile.rs` exactly: `parse_module` per
//! file -> one shared [`Binder`] (`build_file` per file) -> per-file
//! drivers (mechanical fact copies) -> [`ModuleGraph`] over the real
//! relative paths -> [`check_program`]. Helpers are mechanical copies of
//! that file's drivers; duplication across test files is the established
//! pattern (nothing shared is factored out).
//!
//! Acceptance question (V026 flip terms): the `import { isPlainObject }
//! from "./_utils"` binding in `defu.ts` is projected silent (1/33). Any
//! diagnostic or decline attached to that binding's spans revokes the flip
//! to 0/33. The test records either outcome honestly and passes in both
//! cases — a revocation is a successful outcome.

use std::time::Instant;

use pith_frontend::{
    parse_module, CallArgKind as FrontendCallArgKind, EnumValueKind as FrontendEnumValueKind,
    FunctionBodyFact, ImportedName as FrontendImportedName, InitKind as FrontendInitKind,
    ParsedFile, ReturnKind as FrontendReturnKind, SingleReturnFact as FrontendReturn,
};
use pith_ids::{FileId, NodeId, Span, SymbolId};
use pith_queries::{QueryDb, QueryKey, QueryKind};
use pith_solver::{
    multifile::{check_program, AliasShape, ImportUse, ProgramFile, ProgramReport},
    CallArg, CallSite, ConstDecl, DeclKind, EnumMember, EnumMemberValue, EnumShape, FileReport,
    FunctionBody, FunctionDecl, FunctionParam, FunctionReturn, InitKind, InterfaceHeritage,
    InterfaceMember, InterfaceShape, JoinedReturns, NamespaceShape, ObjectInit, ObjectMemberInit,
    ObjectMemberKind,
};
use pith_symbols::{
    multifile::{
        ImportInput, ImportedName, LocalExportInput, ModuleGraph, ModuleInput, ReExportInput,
    },
    Binder, ScopeInput, SymbolInput, UnresolvedInput,
};

/// Builds one shared binder from every parsed file's facts.
fn build_binder_multi(parsed: &[ParsedFile]) -> Binder {
    let mut binder = Binder::new();
    for file in parsed {
        let scopes: Vec<ScopeInput> = file
            .scopes
            .iter()
            .map(|scope| ScopeInput {
                index: scope.index,
                parent: scope.parent,
            })
            .collect();
        let symbols: Vec<SymbolInput> = file
            .symbols
            .iter()
            .map(|symbol| SymbolInput {
                scope: symbol.scope,
                name: symbol.name.clone(),
                span: symbol.span,
                flags: symbol.flags,
            })
            .collect();
        let unresolved: Vec<UnresolvedInput> = file
            .unresolved
            .iter()
            .map(|fact| UnresolvedInput {
                name: fact.name.clone(),
                count: fact.count,
            })
            .collect();
        binder.build_file(file.file, &scopes, &symbols, &unresolved);
    }
    binder
}

/// Maps one frontend initializer kind to the solver's, variant by variant.
fn map_init(kind: FrontendInitKind) -> InitKind {
    match kind {
        FrontendInitKind::Number => InitKind::Number,
        FrontendInitKind::String => InitKind::String,
        FrontendInitKind::Boolean => InitKind::Boolean,
        FrontendInitKind::Null => InitKind::Null,
        FrontendInitKind::Undefined => InitKind::Undefined,
        FrontendInitKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend return-literal kind to the solver's primitive kind.
fn map_return_kind(kind: FrontendReturnKind) -> InitKind {
    match kind {
        FrontendReturnKind::Number => InitKind::Number,
        FrontendReturnKind::String => InitKind::String,
        FrontendReturnKind::Boolean(_) => InitKind::Boolean,
        FrontendReturnKind::Null => InitKind::Null,
        FrontendReturnKind::Undefined => InitKind::Undefined,
        FrontendReturnKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend return-member kind to the solver's member kind.
fn map_member_kind(kind: FrontendReturnKind) -> ObjectMemberKind {
    match kind {
        FrontendReturnKind::Number => ObjectMemberKind::Number,
        FrontendReturnKind::String => ObjectMemberKind::String,
        FrontendReturnKind::Boolean(value) => ObjectMemberKind::Boolean(value),
        FrontendReturnKind::Null => ObjectMemberKind::Null,
        FrontendReturnKind::Undefined => ObjectMemberKind::Undefined,
        FrontendReturnKind::NonLiteral => ObjectMemberKind::NonLiteral,
    }
}

/// Maps one frontend call-argument kind to the solver's primitive kind.
fn map_call_arg_kind(kind: FrontendCallArgKind) -> InitKind {
    match kind {
        FrontendCallArgKind::Number => InitKind::Number,
        FrontendCallArgKind::String => InitKind::String,
        FrontendCallArgKind::Boolean => InitKind::Boolean,
        FrontendCallArgKind::Null => InitKind::Null,
        FrontendCallArgKind::Undefined => InitKind::Undefined,
        FrontendCallArgKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Scope-sensitive span + identity for one declarator.
fn fallback_span(
    parsed: &ParsedFile,
    binder: &Binder,
    symbol_index: u32,
    scope: u32,
) -> (String, Span, Option<SymbolId>) {
    let symbol = &parsed.symbols[usize::try_from(symbol_index).expect("dense symbol index")];
    let id = binder.resolve(parsed.file, scope, &symbol.name);
    let span = id
        .and_then(|id| binder.store().get(id))
        .map_or(symbol.span, |found| found.span);
    (symbol.name.clone(), span, id)
}

/// Slices `source` at a fact span (`None` on skew).
fn slice_of(source: &str, span: Span) -> Option<&str> {
    let lo = usize::try_from(span.lo).ok()?;
    let hi = usize::try_from(span.hi).ok()?;
    source.get(lo..hi)
}

/// Whether sliced text is a bare identifier (the disclosed use seam).
fn is_bare_identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// One file's hand-fed object members: declarator name plus member shapes.
struct ObjectSpec<'a> {
    name: &'a str,
    members: &'a [(&'a str, ObjectMemberKind)],
}

/// The const driver: facts verbatim, plus sliced identifier names and
/// literal spellings (disclosed seams) and object members from the table.
fn consts_from_facts(
    parsed: &ParsedFile,
    binder: &Binder,
    source: &str,
    objects: &[ObjectSpec<'_>],
) -> (Vec<ConstDecl>, Vec<Option<String>>, Vec<Option<String>>) {
    let mut consts = Vec::with_capacity(parsed.decls.len());
    let mut idents = Vec::with_capacity(parsed.decls.len());
    let mut texts = Vec::with_capacity(parsed.decls.len());
    for decl in &parsed.decls {
        let (name, span, symbol) = fallback_span(parsed, binder, decl.symbol, decl.scope);
        let fed = objects.iter().find(|spec| spec.name == name);
        let (init, init_object) = match fed {
            Some(spec) => (
                None,
                Some(ObjectInit {
                    members: spec
                        .members
                        .iter()
                        .map(|(member, kind)| ObjectMemberInit {
                            name: (*member).to_owned(),
                            kind: *kind,
                        })
                        .collect(),
                    fresh: true,
                }),
            ),
            None => (decl.init.as_ref().map(|init| map_init(init.kind)), None),
        };
        let ident = match (&decl.init, fed) {
            (Some(init), None) if init.kind == FrontendInitKind::NonLiteral => {
                slice_of(source, init.span).filter(|text| is_bare_identifier(text))
            }
            _ => None,
        };
        let text = match &decl.init {
            Some(init)
                if matches!(
                    init.kind,
                    FrontendInitKind::Number | FrontendInitKind::String | FrontendInitKind::Boolean
                ) =>
            {
                let sliced =
                    slice_of(source, init.span).unwrap_or_else(|| panic!("literal slices cleanly"));
                assert!(!sliced.is_empty(), "literal init slice is non-empty");
                Some(sliced.to_owned())
            }
            _ => None,
        };
        consts.push(ConstDecl {
            name,
            span,
            scope: decl.scope,
            symbol,
            kind: DeclKind::Const,
            annotation: decl.annotation.as_ref().map(|ann| ann.text.clone()),
            init,
            init_object,
            // No array-member facts yet (see the check-functions driver).
            init_array: None,
            cast: None,
        });
        idents.push(ident.map(str::to_owned));
        texts.push(text);
    }
    (consts, idents, texts)
}

/// Maps one frontend return expression to the solver's return shape.
fn map_function_return(ret: &FrontendReturn) -> FunctionReturn {
    let init_object = ret.members.as_ref().map(|members| ObjectInit {
        members: members
            .iter()
            .map(|member| ObjectMemberInit {
                name: member.name.clone(),
                kind: map_member_kind(member.kind),
            })
            .collect(),
        fresh: true,
    });
    let kind = if init_object.is_some() {
        None
    } else {
        Some(map_return_kind(ret.kind))
    };
    FunctionReturn {
        kind,
        init_object,
        // No array-member facts yet (see the check-functions driver).
        init_array: None,
        cast: None,
    }
}

/// Maps one joined frontend return pair to the solver's joined shape.
fn map_joined(first: &FrontendReturn, second: &FrontendReturn) -> JoinedReturns {
    JoinedReturns {
        first: map_function_return(first),
        second: map_function_return(second),
    }
}

/// The function driver: a mechanical copy of the check-calls driver.
fn functions_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<FunctionDecl> {
    parsed
        .functions
        .iter()
        .map(|func| {
            let (name, span, symbol) = fallback_span(parsed, binder, func.symbol, func.scope);
            let body = match &func.body {
                FunctionBodyFact::SingleReturn(ret) => {
                    FunctionBody::SingleReturn(map_function_return(ret))
                }
                FunctionBodyFact::SequenceReturns { first, second } => {
                    FunctionBody::SequenceReturns(map_joined(first, second))
                }
                FunctionBodyFact::GuardReturn { guard, tail } => {
                    FunctionBody::GuardReturn(map_joined(guard, tail))
                }
                FunctionBodyFact::BranchReturns {
                    then_branch,
                    else_branch,
                } => FunctionBody::BranchReturns(map_joined(then_branch, else_branch)),
                FunctionBodyFact::NoBody { declared } => FunctionBody::NoBody {
                    declared: *declared,
                },
                FunctionBodyFact::Empty => FunctionBody::Empty,
                // P031 straight bodies decline here: no fixture in this
                // suite holds one, so outcomes are unchanged; faithful
                // mapping lives in e2e_check_functions. P039 try/catch
                // bodies decline the same way.
                FunctionBodyFact::StraightBody { .. }
                | FunctionBodyFact::TryCatch { .. }
                | FunctionBodyFact::TryUnsupported { .. }
                | FunctionBodyFact::Switch { .. }
                | FunctionBodyFact::SwitchUnsupported { .. }
                | FunctionBodyFact::Complex => FunctionBody::Complex,
            };
            FunctionDecl {
                name,
                span,
                scope: func.scope,
                symbol,
                params: func
                    .params
                    .iter()
                    .map(|param| FunctionParam {
                        name: param.name.clone(),
                        annotated: param.annotated,
                        annotation: param.annotation_text.clone(),
                        optional: param.optional,
                        is_rest: param.is_rest,
                    })
                    .collect(),
                params_complex: func.params_complex,
                // No async fact yet (see the check-functions driver).
                is_async: false,
                return_annotation: func.return_annotation.as_ref().map(|ann| ann.text.clone()),
                body,
            }
        })
        .collect()
}

/// The call-site driver: a mechanical copy of the check-calls driver.
fn calls_from_facts(parsed: &ParsedFile) -> Vec<CallSite> {
    parsed
        .calls
        .iter()
        .map(|call| CallSite {
            callee: call.callee.clone(),
            callee_span: call.callee_span,
            span: call.span,
            args: call
                .args
                .iter()
                .map(|arg| CallArg {
                    kind: map_call_arg_kind(arg.kind),
                    span: arg.span,
                    cast: None,
                })
                .collect(),
        })
        .collect()
}

/// The interface driver: a mechanical copy of the check-interfaces driver.
fn interfaces_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<InterfaceShape> {
    parsed
        .interfaces
        .iter()
        .map(|fact| {
            let id = binder
                .resolve(parsed.file, fact.scope, &fact.name)
                .unwrap_or_else(|| panic!("interface '{}' links nothing", fact.name));
            InterfaceShape {
                name: fact.name.clone(),
                scope: fact.scope,
                symbol: Some(id),
                span: fact.span,
                members: fact
                    .members
                    .iter()
                    .map(|member| InterfaceMember {
                        name: member.name.clone(),
                        annotation_text: member.annotation_text.clone(),
                        optional: member.optional,
                        span: member.span,
                        complex_reason: member.complex_reason.clone(),
                    })
                    .collect(),
                heritage: fact
                    .heritage
                    .iter()
                    .map(|parent| InterfaceHeritage {
                        name: parent.name.clone(),
                        span: parent.span,
                    })
                    .collect(),
                has_type_params: fact.has_type_params,
                exported: fact.exported,
            }
        })
        .collect()
}

/// Maps one frontend enum value to the solver's, variant by variant.
fn map_enum_value(value: &FrontendEnumValueKind) -> EnumMemberValue {
    match value {
        FrontendEnumValueKind::Number(found) => EnumMemberValue::Number(*found),
        FrontendEnumValueKind::String(found) => EnumMemberValue::String(found.clone()),
        FrontendEnumValueKind::Computed { reason } => EnumMemberValue::Computed {
            reason: reason.clone(),
        },
    }
}

/// The enum/namespace drivers: mechanical copies of the check-enums driver.
fn enums_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<EnumShape> {
    parsed
        .enums
        .iter()
        .map(|fact| {
            let id = binder
                .resolve(parsed.file, fact.scope, &fact.name)
                .unwrap_or_else(|| panic!("enum '{}' links nothing", fact.name));
            EnumShape {
                name: fact.name.clone(),
                scope: fact.scope,
                symbol: Some(id),
                span: fact.span,
                members: fact
                    .members
                    .iter()
                    .map(|member| EnumMember {
                        name: member.name.clone(),
                        value: map_enum_value(&member.value),
                        span: member.span,
                    })
                    .collect(),
                is_const: fact.is_const,
                declared: fact.declared,
                exported: fact.exported,
            }
        })
        .collect()
}

/// The namespace driver: a mechanical copy of the check-enums driver.
fn namespaces_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<NamespaceShape> {
    parsed
        .namespaces
        .iter()
        .map(|fact| {
            let id = binder
                .resolve(parsed.file, fact.scope, &fact.name)
                .unwrap_or_else(|| panic!("namespace '{}' links nothing", fact.name));
            NamespaceShape {
                name: fact.name.clone(),
                scope: fact.scope,
                symbol: Some(id),
                span: fact.span,
                body_scope: fact.body_scope,
                declared: fact.declared,
                exported: fact.exported,
                exported_members: fact.exported_members.clone(),
            }
        })
        .collect()
}

/// The alias driver: a mechanical copy of each alias fact's name plus its
/// sliced target text (spans never sliced driver-side).
fn aliases_from_facts(parsed: &ParsedFile) -> Vec<AliasShape> {
    parsed
        .aliases
        .iter()
        .map(|fact| AliasShape {
            name: fact.name.clone(),
            target: fact.target_text.clone(),
            has_type_params: fact.has_type_params,
        })
        .collect()
}

/// Maps one frontend imported name to the graph's, variant by variant.
fn map_imported_name(name: &FrontendImportedName) -> ImportedName {
    match name {
        FrontendImportedName::Named(found) => ImportedName::Named(found.clone()),
        FrontendImportedName::Default => ImportedName::Default,
        FrontendImportedName::Namespace => ImportedName::Namespace,
    }
}

/// The module driver: import bindings plus graph inputs, all mechanical
/// copies of frontend facts (spans from facts, never sliced text).
fn imports_from_facts(parsed: &ParsedFile) -> (Vec<ImportUse>, ModuleInput) {
    let mut uses = Vec::with_capacity(parsed.named_imports.len());
    let mut inputs = Vec::with_capacity(parsed.named_imports.len());
    for fact in &parsed.named_imports {
        uses.push(ImportUse {
            local: fact.local.clone(),
            imported: map_imported_name(&fact.imported),
            specifier: fact.specifier.clone(),
            scope: fact.scope,
            span: fact.span,
            imported_span: fact.imported_span,
            specifier_span: fact.specifier_span,
            is_type: fact.is_type,
        });
        inputs.push(ImportInput {
            local: fact.local.clone(),
            imported: map_imported_name(&fact.imported),
            specifier: fact.specifier.clone(),
        });
    }
    let module = ModuleInput {
        file: parsed.file,
        path: String::new(),
        imports: inputs,
        local_exports: parsed
            .local_exports
            .iter()
            .map(|fact| LocalExportInput {
                exported: fact.exported.clone(),
                local: fact.local.clone(),
            })
            .collect(),
        reexports: parsed
            .reexports
            .iter()
            .map(|fact| ReExportInput {
                exported: fact.exported.clone(),
                imported: fact.imported.clone(),
                specifier: fact.specifier.clone(),
            })
            .collect(),
    };
    (uses, module)
}

/// One program file for the driver: path, source, and hand-fed objects.
struct FileSpec<'a> {
    path: &'a str,
    source: &'a str,
    objects: &'a [ObjectSpec<'a>],
}

/// A checked real program: verdict, memo store, graph, and stage walls.
struct Program {
    report: ProgramReport,
    db: QueryDb,
    binder: Binder,
    graph: ModuleGraph,
    parsed: Vec<ParsedFile>,
    parse_bind_ms: u128,
    check_ms: u128,
}

/// Runs the full multi-file pipeline on one program: parse every file,
/// build the shared binder, adapt drivers, resolve the graph, check.
fn run_program(specs: &[FileSpec<'_>]) -> Program {
    let parse_start = Instant::now();
    let mut parsed = Vec::with_capacity(specs.len());
    for (index, spec) in specs.iter().enumerate() {
        let file = FileId(u32::try_from(index).expect("small program"));
        let file_parsed = parse_module(file, spec.path, spec.source);
        let errors = &file_parsed.errors;
        assert!(file_parsed.errors.is_empty(), "frontend errors: {errors:?}");
        parsed.push(file_parsed);
    }
    let binder = build_binder_multi(&parsed);
    let mut files = Vec::with_capacity(parsed.len());
    let mut modules = Vec::with_capacity(parsed.len());
    for (file_parsed, spec) in parsed.iter().zip(specs.iter()) {
        let (consts, idents, texts) =
            consts_from_facts(file_parsed, &binder, spec.source, spec.objects);
        let (uses, mut module) = imports_from_facts(file_parsed);
        spec.path.clone_into(&mut module.path);
        modules.push(module);
        files.push(ProgramFile {
            file: file_parsed.file,
            consts,
            ident_inits: idents,
            enum_texts: texts,
            functions: functions_from_facts(file_parsed, &binder),
            calls: calls_from_facts(file_parsed),
            interfaces: interfaces_from_facts(file_parsed, &binder),
            enums: enums_from_facts(file_parsed, &binder),
            namespaces: namespaces_from_facts(file_parsed, &binder),
            aliases: aliases_from_facts(file_parsed),
            imports: uses,
        });
    }
    let graph = ModuleGraph::new(modules);
    let parse_bind_ms = parse_start.elapsed().as_millis();
    let check_start = Instant::now();
    let mut db = QueryDb::new();
    let report = check_program(&files, &graph, &binder, &mut db);
    let check_ms = check_start.elapsed().as_millis();
    Program {
        report,
        db,
        binder,
        graph,
        parsed,
        parse_bind_ms,
        check_ms,
    }
}

/// The pinned defu file set (paths mirror the corpus layout so `./_utils`
/// and `./types` resolve through [`ModuleGraph`]).
fn defu_specs() -> [FileSpec<'static>; 3] {
    [
        FileSpec {
            path: "defu/src/_utils.ts",
            source: include_str!("../../../corpus/real/defu/src/_utils.ts"),
            objects: &[],
        },
        FileSpec {
            path: "defu/src/types.ts",
            source: include_str!("../../../corpus/real/defu/src/types.ts"),
            objects: &[],
        },
        FileSpec {
            path: "defu/src/defu.ts",
            source: include_str!("../../../corpus/real/defu/src/defu.ts"),
            objects: &[],
        },
    ]
}

/// The executed verdict on the defu value import (PITH-P027).
///
/// The V026 projection says `import { isPlainObject } from "./_utils"` in
/// `defu.ts` checks silent (1/33). Silence means NO diagnostic and NO
/// unsupported note anchored at either of the binding's spans (the local
/// span or the imported-name span). Anything attached revokes to 0/33.
/// The test passes in both cases and prints `DEFU_IMPORT_VERDICT` so the
/// remote run output is the evidence; a revocation is a success.
#[test]
fn real_defu_value_import_verdict() {
    let specs = defu_specs();
    let program = run_program(&specs);
    assert_eq!(program.report.files.len(), 3, "defu graph file count");
    // The import binding's spans, straight from the adapter facts.
    let defu_parsed = &program.parsed[2];
    let import = defu_parsed
        .named_imports
        .iter()
        .find(|fact| fact.local == "isPlainObject")
        .expect("defu.ts imports isPlainObject");
    assert_eq!(import.specifier, "./_utils");
    assert!(!import.is_type, "value import, not import type");
    // Resolution premise (not the verdict): the graph must see the facted
    // export. The verdict below is recorded, never forced.
    assert!(
        program
            .graph
            .resolve_import(FileId(2), "isPlainObject")
            .is_ok(),
        "isPlainObject resolves through the defu graph",
    );
    let main = program.report.file(FileId(2)).expect("defu.ts report");
    let attached_diags: Vec<String> = main
        .diagnostics
        .iter()
        .filter(|diag| diag.span == import.span || Some(diag.span) == import.imported_span)
        .map(|diag| {
            let code = diag.code.as_str();
            let message = diag.message.as_str();
            format!("{code}: {message}")
        })
        .collect();
    let attached_notes: Vec<String> = main
        .unsupported
        .iter()
        .filter(|note| note.span == import.span || Some(note.span) == import.imported_span)
        .map(|note| note.reason.clone())
        .collect();
    for (file, report) in &program.report.files {
        let diags = report.diagnostics.len();
        let notes = report.unsupported.len();
        println!("DEFU_FILE {file:?}: {diags} diagnostics, {notes} unsupported");
        for diag in &report.diagnostics {
            let code = diag.code.as_str();
            let message = diag.message.as_str();
            println!("DEFU_DIAG {file:?}: {code}: {message}");
        }
        for note in &report.unsupported {
            let reason = note.reason.as_str();
            println!("DEFU_NOTE {file:?}: {reason}");
        }
        let mut spans: Vec<Span> = report.diagnostics.iter().map(|diag| diag.span).collect();
        spans.extend(report.unsupported.iter().map(|note| note.span));
        for item in spans {
            assert!(item.lo < item.hi, "degenerate span in {file:?}");
        }
    }
    let parse_bind_ms = program.parse_bind_ms;
    let check_ms = program.check_ms;
    println!("DEFU_WALL_MS parse_bind={parse_bind_ms} check={check_ms}");
    if attached_diags.is_empty() && attached_notes.is_empty() {
        println!("DEFU_IMPORT_VERDICT: CONFIRM silent (1/33 holds)");
    } else {
        println!(
            "DEFU_IMPORT_VERDICT: REVOKE to 0/33 — \
             diagnostics={attached_diags:?} unsupported={attached_notes:?}",
        );
    }
    // Memo signal (informational only, never asserted): unannotated consts
    // decline in `check_one` before the `TypeOf` insert by design, and all
    // three defu consts are unannotated (casts are not a fed seam), so a
    // missing entry there is an established path, not a silent skip. Files
    // whose first const carries an annotation are expected to memoize.
    for (index, file_parsed) in program.parsed.iter().enumerate() {
        if file_parsed.decls.is_empty() {
            continue;
        }
        let file = FileId(u32::try_from(index).expect("small program"));
        let memoized = program
            .db
            .cached_deps(&QueryKey {
                file,
                node: NodeId(0),
                kind: QueryKind::TypeOf,
            })
            .is_some();
        println!("DEFU_MEMO {file:?}: node0 memoized={memoized}");
    }
}

/// The pinned destr file set: one file, so the graph holds a single
/// module and no imports (the premise the test below asserts).
fn destr_specs() -> [FileSpec<'static>; 1] {
    [FileSpec {
        path: "destr/src/index.ts",
        source: include_str!("../../../corpus/real/destr/src/index.ts"),
        objects: &[],
    }]
}

/// The executed verdict on the destr graph (PITH-P028).
///
/// The v2 prescan projects `jsonParseTransform` declines (a bare return
/// plus a two-statement branch, not `GuardReturn`) and 0/9 overall. A
/// decline at the target's span confirms the projection; a silent check
/// or a diagnostic flips it. The test passes in every case and prints
/// `DESTR_TARGET_VERDICT` so the remote run output is the evidence — a
/// flip is data, not failure. Every `DESTR_*` line reports an EXECUTED
/// value; the projection is quoted only for comparison, never as a
/// verdict.
///
/// The nearest-miss target plus whatever the run attached at its span.
struct TargetVerdict {
    diags: Vec<String>,
    notes: Vec<String>,
}

/// Locates `jsonParseTransform` in the adapter facts and collects whatever
/// the executed run attached at its span (or silence).
fn destr_target_verdict(
    destr_parsed: &ParsedFile,
    binder: &Binder,
    main: &FileReport,
) -> TargetVerdict {
    let target = destr_parsed
        .functions
        .iter()
        .find(|func| {
            let index = usize::try_from(func.symbol).expect("dense symbol index");
            destr_parsed.symbols[index].name == "jsonParseTransform"
        })
        .expect("destr defines jsonParseTransform");
    let (target_name, target_span, _) =
        fallback_span(destr_parsed, binder, target.symbol, target.scope);
    assert_eq!(target_name, "jsonParseTransform");
    let diags = main
        .diagnostics
        .iter()
        .filter(|diag| diag.span == target_span)
        .map(|diag| {
            let code = diag.code.as_str();
            let message = diag.message.as_str();
            format!("{code}: {message}")
        })
        .collect();
    let notes = main
        .unsupported
        .iter()
        .filter(|note| note.span == target_span)
        .map(|note| note.reason.clone())
        .collect();
    TargetVerdict { diags, notes }
}

/// Prints one EXECUTED line per fed function and const: whatever the run
/// attached at its span (diagnosed, declined with reasons, or silence).
fn print_construct_verdicts(destr_parsed: &ParsedFile, binder: &Binder, main: &FileReport) {
    for func in &destr_parsed.functions {
        let (name, span, _) = fallback_span(destr_parsed, binder, func.symbol, func.scope);
        let diags = main
            .diagnostics
            .iter()
            .filter(|diag| diag.span == span)
            .count();
        let notes: Vec<&str> = main
            .unsupported
            .iter()
            .filter(|note| note.span == span)
            .map(|note| note.reason.as_str())
            .collect();
        if diags > 0 {
            println!("DESTR_FUNC {name}: EXECUTED diagnosed x{diags}");
        } else if notes.is_empty() {
            println!("DESTR_FUNC {name}: EXECUTED silent");
        } else {
            println!("DESTR_FUNC {name}: EXECUTED declined {notes:?}");
        }
    }
    for decl in &destr_parsed.decls {
        let (name, span, _) = fallback_span(destr_parsed, binder, decl.symbol, decl.scope);
        let diags = main
            .diagnostics
            .iter()
            .filter(|diag| diag.span == span)
            .count();
        let notes: Vec<&str> = main
            .unsupported
            .iter()
            .filter(|note| note.span == span)
            .map(|note| note.reason.as_str())
            .collect();
        if diags > 0 {
            println!("DESTR_CONST {name}: EXECUTED diagnosed x{diags}");
        } else if notes.is_empty() {
            println!("DESTR_CONST {name}: EXECUTED silent");
        } else {
            println!("DESTR_CONST {name}: EXECUTED declined {notes:?}");
        }
    }
}

/// Dumps per-file verdict counts plus every diagnostic and note, and
/// asserts span hygiene — mirroring the DEFU protocol.
fn dump_file_verdicts(program: &Program) {
    for (file, report) in &program.report.files {
        let diags = report.diagnostics.len();
        let notes = report.unsupported.len();
        println!("DESTR_FILE {file:?}: {diags} diagnostics, {notes} unsupported");
        for diag in &report.diagnostics {
            let code = diag.code.as_str();
            let message = diag.message.as_str();
            println!("DESTR_DIAG {file:?}: {code}: {message}");
        }
        for note in &report.unsupported {
            let reason = note.reason.as_str();
            println!("DESTR_NOTE {file:?}: {reason}");
        }
        let mut spans: Vec<Span> = report.diagnostics.iter().map(|diag| diag.span).collect();
        spans.extend(report.unsupported.iter().map(|note| note.span));
        for item in spans {
            assert!(item.lo < item.hi, "degenerate span in {file:?}");
        }
    }
}

#[test]
fn real_destr_single_file_verdict() {
    let specs = destr_specs();
    let program = run_program(&specs);
    assert_eq!(program.report.files.len(), 1, "destr graph file count");
    // Single-file premise (not a verdict): nothing to import or resolve.
    let destr_parsed = &program.parsed[0];
    assert!(
        destr_parsed.named_imports.is_empty(),
        "destr premise: no imports expected",
    );
    assert!(
        destr_parsed.reexports.is_empty(),
        "destr premise: no re-exports expected",
    );
    // The nearest-miss target, straight from the adapter facts.
    let main = program.report.file(FileId(0)).expect("destr report");
    let target = destr_target_verdict(destr_parsed, &program.binder, main);
    let attached_diags = target.diags;
    let attached_notes = target.notes;
    // Per-construct EXECUTED verdicts: every fed function and const maps
    // its span to whatever the run attached there (or silence).
    print_construct_verdicts(destr_parsed, &program.binder, main);
    // Full-file dump plus span hygiene, mirroring the DEFU protocol.
    dump_file_verdicts(&program);
    let parse_bind_ms = program.parse_bind_ms;
    let check_ms = program.check_ms;
    println!("DESTR_WALL_MS parse_bind={parse_bind_ms} check={check_ms}");
    println!("DESTR_PROJECTION: jsonParseTransform declines (bare return, v2 #4)");
    if attached_diags.is_empty() && attached_notes.is_empty() {
        println!("DESTR_TARGET_VERDICT: EXECUTED silent — FLIP vs projection");
    } else if attached_diags.is_empty() {
        println!(
            "DESTR_TARGET_VERDICT: EXECUTED decline — \
             CONFIRMS projection {attached_notes:?}",
        );
    } else {
        println!(
            "DESTR_TARGET_VERDICT: EXECUTED diagnosed — FLIP vs projection \
             {attached_diags:?} {attached_notes:?}",
        );
    }
}

/// The pinned plimit file set: one ambient `.d.ts`, so the graph holds a
/// single module and no imports (the premise the test below asserts).
fn plimit_specs() -> [FileSpec<'static>; 1] {
    [FileSpec {
        path: "plimit-stress/index.d.ts",
        source: include_str!("../../../corpus/real/plimit-stress/index.d.ts"),
        objects: &[],
    }]
}

/// The ambient target plus whatever the run attached at its span.
struct PlimitTarget {
    diags: Vec<String>,
    notes: Vec<String>,
}

/// Locates `pLimit` in the adapter facts and collects whatever the
/// executed run attached at its span (or silence).
fn plimit_target_verdict(parsed: &ParsedFile, binder: &Binder, main: &FileReport) -> PlimitTarget {
    let target = parsed
        .functions
        .iter()
        .find(|func| {
            let index = usize::try_from(func.symbol).expect("dense symbol index");
            parsed.symbols[index].name == "pLimit"
        })
        .expect("plimit defines pLimit");
    let (name, span, _) = fallback_span(parsed, binder, target.symbol, target.scope);
    assert_eq!(name, "pLimit");
    let diags = main
        .diagnostics
        .iter()
        .filter(|diag| diag.span == span)
        .map(|diag| {
            let code = diag.code.as_str();
            let message = diag.message.as_str();
            format!("{code}: {message}")
        })
        .collect();
    let notes = main
        .unsupported
        .iter()
        .filter(|note| note.span == span)
        .map(|note| note.reason.clone())
        .collect();
    PlimitTarget { diags, notes }
}

/// Prints one EXECUTED line per fed function at its span.
fn print_plimit_functions(parsed: &ParsedFile, binder: &Binder, main: &FileReport) {
    for func in &parsed.functions {
        let (name, span, _) = fallback_span(parsed, binder, func.symbol, func.scope);
        let diags = main
            .diagnostics
            .iter()
            .filter(|diag| diag.span == span)
            .count();
        let notes: Vec<&str> = main
            .unsupported
            .iter()
            .filter(|note| note.span == span)
            .map(|note| note.reason.as_str())
            .collect();
        if diags > 0 {
            println!("PLIMIT_FUNC {name}: EXECUTED diagnosed x{diags}");
        } else if notes.is_empty() {
            println!("PLIMIT_FUNC {name}: EXECUTED silent");
        } else {
            println!("PLIMIT_FUNC {name}: EXECUTED declined {notes:?}");
        }
    }
}

/// Prints one EXECUTED line per fed const at its span.
fn print_plimit_consts(parsed: &ParsedFile, binder: &Binder, main: &FileReport) {
    for decl in &parsed.decls {
        let (name, span, _) = fallback_span(parsed, binder, decl.symbol, decl.scope);
        let diags = main
            .diagnostics
            .iter()
            .filter(|diag| diag.span == span)
            .count();
        let notes: Vec<&str> = main
            .unsupported
            .iter()
            .filter(|note| note.span == span)
            .map(|note| note.reason.as_str())
            .collect();
        if diags > 0 {
            println!("PLIMIT_CONST {name}: EXECUTED diagnosed x{diags}");
        } else if notes.is_empty() {
            println!("PLIMIT_CONST {name}: EXECUTED silent");
        } else {
            println!("PLIMIT_CONST {name}: EXECUTED declined {notes:?}");
        }
    }
}

/// Prints one EXECUTED line per fed interface at its span.
fn print_plimit_interfaces(parsed: &ParsedFile, main: &FileReport) {
    for fact in &parsed.interfaces {
        let diags = main
            .diagnostics
            .iter()
            .filter(|diag| diag.span == fact.span)
            .count();
        let notes: Vec<&str> = main
            .unsupported
            .iter()
            .filter(|note| note.span == fact.span)
            .map(|note| note.reason.as_str())
            .collect();
        let name = fact.name.as_str();
        if diags > 0 {
            println!("PLIMIT_INTERFACE {name}: EXECUTED diagnosed x{diags}");
        } else if notes.is_empty() {
            println!("PLIMIT_INTERFACE {name}: EXECUTED silent");
        } else {
            println!("PLIMIT_INTERFACE {name}: EXECUTED declined {notes:?}");
        }
    }
}

/// Prints every fed per-construct EXECUTED verdict for the plimit graph.
///
/// Type aliases (`LimitFunction`, `Options`) emit no facts per the P022
/// precedent, so they carry no fed span to verdict; the three families
/// above are the exhaustive fed per-construct surface.
fn print_plimit_verdicts(parsed: &ParsedFile, binder: &Binder, main: &FileReport) {
    print_plimit_functions(parsed, binder, main);
    print_plimit_consts(parsed, binder, main);
    print_plimit_interfaces(parsed, main);
}

/// Dumps per-file verdict counts plus every diagnostic and note, and
/// asserts span hygiene — mirroring the DESTR protocol.
fn dump_plimit_file(program: &Program) {
    for (file, report) in &program.report.files {
        let diags = report.diagnostics.len();
        let notes = report.unsupported.len();
        println!("PLIMIT_FILE {file:?}: {diags} diagnostics, {notes} unsupported");
        for diag in &report.diagnostics {
            let code = diag.code.as_str();
            let message = diag.message.as_str();
            println!("PLIMIT_DIAG {file:?}: {code}: {message}");
        }
        for note in &report.unsupported {
            let reason = note.reason.as_str();
            println!("PLIMIT_NOTE {file:?}: {reason}");
        }
        let mut spans: Vec<Span> = report.diagnostics.iter().map(|diag| diag.span).collect();
        spans.extend(report.unsupported.iter().map(|note| note.span));
        for item in spans {
            assert!(item.lo < item.hi, "degenerate span in {file:?}");
        }
    }
}

/// The executed verdict on the plimit graph (PITH-P029).
///
/// The v2 prescan projects wholesale decline on ambient/declare forms
/// (0/4). A decline at the `pLimit` span confirms the projection; a
/// silent check or a diagnostic flips it. The test passes in every case
/// and prints `PLIMIT_TARGET_VERDICT` so the remote run output is the
/// evidence — any outcome is a successful measurement. Every `PLIMIT_*`
/// line reports an EXECUTED value; the projection is quoted only for
/// comparison, never as a verdict.
#[test]
fn real_plimit_blowup_verdict() {
    let specs = plimit_specs();
    let program = run_program(&specs);
    assert_eq!(program.report.files.len(), 1, "plimit graph file count");
    // Single-file premise (not a verdict): the `.d.ts` carries no imports
    // or re-exports — asserted after reading the file, not assumed.
    let parsed = &program.parsed[0];
    assert!(
        parsed.named_imports.is_empty(),
        "plimit premise: no imports"
    );
    assert!(parsed.reexports.is_empty(), "plimit premise: no re-exports");
    // The ambient target, straight from the adapter facts.
    let main = program.report.file(FileId(0)).expect("plimit report");
    let target = plimit_target_verdict(parsed, &program.binder, main);
    let attached_diags = target.diags;
    let attached_notes = target.notes;
    // Per-construct EXECUTED verdicts plus the full-file dump and hygiene.
    print_plimit_verdicts(parsed, &program.binder, main);
    dump_plimit_file(&program);
    let parse_bind_ms = program.parse_bind_ms;
    let check_ms = program.check_ms;
    println!("PLIMIT_WALL_MS parse_bind={parse_bind_ms} check={check_ms}");
    println!("PLIMIT_PROJECTION: wholesale decline on ambient forms (v2 0/4)");
    if attached_diags.is_empty() && attached_notes.is_empty() {
        println!("PLIMIT_TARGET_VERDICT: EXECUTED silent — FLIP vs projection");
    } else if attached_diags.is_empty() {
        println!(
            "PLIMIT_TARGET_VERDICT: EXECUTED decline — \
             CONFIRMS projection {attached_notes:?}",
        );
    } else {
        println!(
            "PLIMIT_TARGET_VERDICT: EXECUTED diagnosed — FLIP vs projection \
             {attached_diags:?} {attached_notes:?}",
        );
    }
}
