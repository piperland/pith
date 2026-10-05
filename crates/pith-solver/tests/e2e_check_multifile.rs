//! Fact-fed solver end-to-end (PITH-P019): multi-file programs.
//!
//! Pipeline per program: `parse_module` per file -> one shared
//! [`Binder`] (`build_file` per file) -> per-file drivers (declaration
//! names, scopes, spans, annotation texts, literal kinds, call facts, and
//! shape facts verbatim from adapter facts; module facts into
//! [`ModuleGraph`] inputs) -> [`check_program`] -> [`ProgramReport`], then
//! a differential against the recorded tsc `.expected.txt` baselines plus
//! the cross-file invalidation demo.
//!
//! Division of labor: everything structural comes from adapter facts. The
//! ONLY driver-side mappings are the mechanical enum translations
//! (frontend literal kinds to solver kinds, import/export entries to graph
//! inputs) plus three disclosed seams the adapter cannot feed yet (no
//! expression facts — the narrowing/check-enums precedents):
//!
//! - identifier-initializer names ([`ProgramFile::ident_inits`]): the init
//!   span must slice to a bare identifier, else the decl keeps its
//!   `NonLiteral` verdict path;
//! - enum literal spellings ([`ProgramFile::enum_texts`]): the init span
//!   slice for literal inits, `None` elsewhere (those paths never read it);
//! - object-literal members: per-fixture `(name, members)` tables keyed by
//!   declarator name (spans/scopes/annotations still from facts; decls with
//!   fed members check with `init: None`, exactly like the check-object
//!   `HandFed` specs).
//!
//! Differential rule: oracle lines are `file:TSNNNN: message`, compared per
//! file as sorted `(numeric-code, message)` multisets (`TS2305` <->
//! `PITH2305`, `TS2307` <-> `PITH2307`, plus the earlier families) with the
//! expected unsupported count. The invalidation demo asserts exact
//! drop-counts on one shared [`QueryDb`]: editing the shared declaration
//! invalidates its own plus its dependents' entries and nothing else, while
//! a leaf edit drops exactly one entry.

use pith_frontend::{
    parse_module, CallArgKind as FrontendCallArgKind, EnumValueKind as FrontendEnumValueKind,
    FunctionBodyFact, ImportedName as FrontendImportedName, InitKind as FrontendInitKind,
    ParsedFile, ReturnKind as FrontendReturnKind, SingleReturnFact as FrontendReturn,
};
use pith_ids::{FileId, NodeId, Span, SymbolId};
use pith_queries::{Dep, QueryDb, QueryKey, QueryKind};
use pith_solver::{
    multifile::{
        check_program, AliasShape, ImportUse, ProgramFile, ProgramReport, CODE_NO_EXPORTED,
        CODE_NO_MODULE,
    },
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
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
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

/// Maps one frontend return-member kind to the solver's member kind,
/// preserving the boolean payload for tsc's fresh-literal spelling.
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

/// Scope-sensitive span + identity for one declarator, mirroring the
/// check-const driver.
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

/// Slices `source` at a fact span (`None` on skew — only possible with
/// recovery from parse errors).
fn slice_of(source: &str, span: Span) -> Option<&str> {
    let lo = usize::try_from(span.lo).ok()?;
    let hi = usize::try_from(span.hi).ok()?;
    source.get(lo..hi)
}

/// Whether sliced text is a bare identifier (the disclosed use seam —
/// mirrors the narrowing driver's check).
fn is_bare_identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// One file's hand-fed object members: declarator name plus member shapes.
///
/// `init: None` with members is the check-object convention (the adapter
/// emits no member facts, so fed members override the fact's `NonLiteral`
/// kind exactly like the `HandFed` specs do).
struct ObjectSpec<'a> {
    name: &'a str,
    members: &'a [(&'a str, ObjectMemberKind)],
}

/// The const driver: names/scopes/spans/annotations/kinds from adapter
/// facts, plus identifier names and literal spellings sliced at fact spans
/// (disclosed seams) and object members from the per-file table.
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
                let sliced = slice_of(source, init.span)
                    .unwrap_or_else(|| panic!("literal init slices cleanly"));
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
            init_ident: None,
            init_object,
            // No array-member facts yet (see the check-functions driver).
            init_array: None,
            cast: None,
            init_ternary: None,
            init_member_ref: None,
            init_arrow: None,
        });
        idents.push(ident.map(str::to_owned));
        texts.push(text);
    }
    (consts, idents, texts)
}

/// Maps one frontend return expression to the solver's return shape.
///
/// Object returns become member facts (always fresh: only direct syntactic
/// literals carry them); every other return becomes its literal kind.
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
        // Bare-identifier tails stay `None` here (see the check-functions
        // driver): only guard-effect tails resolve through P048.
        init_ident: None,
        init_object,
        // No array-member facts yet (see the check-functions driver).
        init_array: None,
        cast: None,
        ternary: None,
        member_ref: None,
    }
}

/// Maps one joined frontend return pair to the solver's joined shape
/// (P023 joins map faithfully in every pipeline).
fn map_joined(first: &FrontendReturn, second: &FrontendReturn) -> JoinedReturns {
    JoinedReturns {
        first: map_function_return(first),
        second: map_function_return(second),
    }
}

/// The function driver: a mechanical copy of the check-calls driver
/// (P023 joins map faithfully, like the check-functions driver).
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
                // bodies, P041 counted-`for` bodies, P043 throw bodies,
                // P045 else-if chains, and P050 guard chains decline the
                // same way.
                FunctionBodyFact::StraightBody { .. }
                | FunctionBodyFact::TryCatch { .. }
                | FunctionBodyFact::TryUnsupported { .. }
                | FunctionBodyFact::Switch { .. }
                | FunctionBodyFact::SwitchUnsupported { .. }
                | FunctionBodyFact::CountedFor { .. }
                | FunctionBodyFact::LoopUnsupported { .. }
                | FunctionBodyFact::GuardThrow { .. }
                | FunctionBodyFact::StraightThrow { .. }
                | FunctionBodyFact::ElseIfChain { .. }
                | FunctionBodyFact::ElseIfUnsupported { .. }
                | FunctionBodyFact::GuardChain { .. }
                | FunctionBodyFact::GuardChainUnsupported { .. }
                | FunctionBodyFact::EffectOnly { .. }
                | FunctionBodyFact::GuardEffect { .. }
                | FunctionBodyFact::EffectUnsupported { .. }
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
                        // No default-kind facts here (the check-functions
                        // driver owns the P070 mapping): `None` keeps the
                        // historical optional decline.
                        default_kind: None,
                    })
                    .collect(),
                params_complex: func.params_complex,
                // No async fact yet (see the check-functions driver).
                is_async: false,
                has_type_params: !func.type_params.is_empty() || func.type_params_complex,
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
                    // Non-generic call drivers never feed identifier names.
                    ident: None,
                    // Call drivers never feed object members.
                    arg_object: None,
                    // Call drivers never feed arrow expressions.
                    arg_arrow: None,
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

/// A checked program: verdict plus the shared memo store for the
/// invalidation demo.
struct Program {
    report: ProgramReport,
    db: QueryDb,
}

/// Runs the full multi-file pipeline on one program: parse every file,
/// build the shared binder, adapt drivers, resolve the graph, check.
fn run_program(specs: &[FileSpec<'_>]) -> Program {
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
    let mut db = QueryDb::new();
    let report = check_program(&files, &graph, &binder, &mut db);
    Program { report, db }
}

/// Parses normalized oracle lines (`file:TSNNNN: message`) into sorted
/// `(numeric-code, message)` pairs; spans/positions are already folded away.
fn parse_baseline(expected: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = expected
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            let mut parts = line.splitn(3, ':');
            let _file = parts.next().unwrap_or("");
            let code = parts.next().unwrap_or("").trim().to_owned();
            let message = parts.next().unwrap_or("").trim().to_owned();
            (code, message)
        })
        .collect();
    out.sort();
    out
}

/// Asserts one file's verdict differentially equals its recorded baseline:
/// same `(code-family, message)` multiset (`TS`/`PITH` prefixes folded) and
/// the expected unsupported count, with sane anchored spans throughout.
fn expect_file(name: &str, report: &FileReport, expected: &str, unsupported: usize) {
    let mut actual: Vec<(String, String)> = report
        .diagnostics
        .iter()
        .map(|diag| {
            let family = diag
                .code
                .strip_prefix("PITH")
                .unwrap_or(diag.code.as_str())
                .to_owned();
            (format!("TS{family}"), diag.message.clone())
        })
        .collect();
    actual.sort();
    let want = parse_baseline(expected);
    assert_eq!(
        actual, want,
        "{name}: pipeline diagnostics diverge from oracle baseline"
    );
    let notes = &report.unsupported;
    assert_eq!(
        report.unsupported.len(),
        unsupported,
        "{name}: unsupported count: {notes:?}"
    );
    for diag in &report.diagnostics {
        assert!(diag.span.lo < diag.span.hi, "{name}: degenerate span");
    }
    for note in &report.unsupported {
        assert!(note.span.lo < note.span.hi, "{name}: degenerate span");
    }
}

/// Asserts the pipeline verdict differentially equals the recorded baseline
/// for every file of a corpus case.
fn expect_case(name: &str, program: &Program, baselines: &[(FileId, &str, usize)]) {
    assert_eq!(
        program.report.files.len(),
        baselines.len(),
        "{name}: file count"
    );
    for (file, expected, unsupported) in baselines {
        let report = program
            .report
            .file(*file)
            .unwrap_or_else(|| panic!("{name}: missing report for file {file:?}"));
        expect_file(name, report, expected, *unsupported);
    }
}

#[test]
fn clean_multifile_matches_empty_baselines() {
    let program = run_program(&[
        FileSpec {
            path: "clean-shared.ts",
            source: include_str!("../../../corpus/check-multifile/clean-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "clean-main.ts",
            source: include_str!("../../../corpus/check-multifile/clean-main.ts"),
            objects: &[ObjectSpec {
                name: "p",
                members: &[
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::Number),
                ],
            }],
        },
    ]);
    expect_case(
        "clean",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/clean-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/clean-main.expected.txt"),
                0,
            ),
        ],
    );
}

#[test]
fn error_multifile_matches_ts2322_and_ts2345() {
    let program = run_program(&[
        FileSpec {
            path: "error-shared.ts",
            source: include_str!("../../../corpus/check-multifile/error-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "error-main.ts",
            source: include_str!("../../../corpus/check-multifile/error-main.ts"),
            objects: &[],
        },
    ]);
    expect_case(
        "error",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/error-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/error-main.expected.txt"),
                0,
            ),
        ],
    );
}

#[test]
fn missing_multifile_matches_ts2305_and_ts2307() {
    let program = run_program(&[
        FileSpec {
            path: "missing-shared.ts",
            source: include_str!("../../../corpus/check-multifile/missing-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "missing-main.ts",
            source: include_str!("../../../corpus/check-multifile/missing-main.ts"),
            objects: &[],
        },
    ]);
    expect_case(
        "missing",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/missing-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/missing-main.expected.txt"),
                0,
            ),
        ],
    );
}

#[test]
fn reexport_chain_resolves_transitively() {
    let program = run_program(&[
        FileSpec {
            path: "chain-shared.ts",
            source: include_str!("../../../corpus/check-multifile/chain-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "chain-mid.ts",
            source: include_str!("../../../corpus/check-multifile/chain-mid.ts"),
            objects: &[],
        },
        FileSpec {
            path: "chain-main.ts",
            source: include_str!("../../../corpus/check-multifile/chain-main.ts"),
            objects: &[],
        },
    ]);
    expect_case(
        "chain",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/chain-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/chain-mid.expected.txt"),
                0,
            ),
            (
                FileId(2),
                include_str!("../../../corpus/check-multifile/chain-main.expected.txt"),
                0,
            ),
        ],
    );
}

#[test]
fn barrel_star_resolves_transitively() {
    let program = run_program(&[
        FileSpec {
            path: "barrel-shared.ts",
            source: include_str!("../../../corpus/check-multifile/barrel-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "barrel-index.ts",
            source: include_str!("../../../corpus/check-multifile/barrel-index.ts"),
            objects: &[],
        },
        FileSpec {
            path: "barrel-main.ts",
            source: include_str!("../../../corpus/check-multifile/barrel-main.ts"),
            objects: &[],
        },
    ]);
    expect_case(
        "barrel",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/barrel-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/barrel-index.expected.txt"),
                0,
            ),
            (
                FileId(2),
                include_str!("../../../corpus/check-multifile/barrel-main.expected.txt"),
                0,
            ),
        ],
    );
}

/// Checked values end-to-end (PITH-P022): a defu-shaped 3-file program
/// (main plus two leaves, mirroring `defu.ts` -> {`_utils.ts`, `types.ts`})
/// where imported const/function/interface/enum values check at use sites
/// with correct types, plus one `TS2322` and one `TS2345` at the
/// intentional errors. Every file carries an honest verdict (diagnostics or
/// a checked-clean bill — never a silent skip): the test additionally
/// asserts each file memoized at least its first const, proving every file
/// was checked rather than skipped.
#[test]
fn checked_value_multifile_matches_baselines() {
    let program = run_program(&[
        FileSpec {
            path: "checked-utils.ts",
            source: include_str!("../../../corpus/check-multifile/checked-utils.ts"),
            objects: &[],
        },
        FileSpec {
            path: "checked-types.ts",
            source: include_str!("../../../corpus/check-multifile/checked-types.ts"),
            objects: &[],
        },
        FileSpec {
            path: "checked-main.ts",
            source: include_str!("../../../corpus/check-multifile/checked-main.ts"),
            objects: &[ObjectSpec {
                name: "p",
                members: &[
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::Number),
                ],
            }],
        },
    ]);
    expect_case(
        "checked-value",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/checked-utils.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/checked-types.expected.txt"),
                0,
            ),
            (
                FileId(2),
                include_str!("../../../corpus/check-multifile/checked-main.expected.txt"),
                0,
            ),
        ],
    );
    for file in [FileId(0), FileId(1), FileId(2)] {
        assert!(
            program
                .db
                .cached_deps(&QueryKey {
                    file,
                    node: NodeId(0),
                    kind: QueryKind::TypeOf,
                })
                .is_some(),
            "file {file:?} memoized nothing: silent skip"
        );
    }
}

/// Invalidation on the defu-shaped graph (PITH-P022): editing the shared
/// types leaf drops exactly its own entry plus its one dependent in main,
/// while a leaf edit inside main drops exactly its own entry.
#[test]
fn defu_graph_invalidation_leaf_vs_shared() {
    let mut program = run_program(&[
        FileSpec {
            path: "checked-utils.ts",
            source: include_str!("../../../corpus/check-multifile/checked-utils.ts"),
            objects: &[],
        },
        FileSpec {
            path: "checked-types.ts",
            source: include_str!("../../../corpus/check-multifile/checked-types.ts"),
            objects: &[],
        },
        FileSpec {
            path: "checked-main.ts",
            source: include_str!("../../../corpus/check-multifile/checked-main.ts"),
            objects: &[ObjectSpec {
                name: "p",
                members: &[
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::Number),
                ],
            }],
        },
    ]);
    // The cross-file edge: main's `x` (const index 4) records the declaring
    // occurrence of `ORIGIN_X` (the only const of checked-types.ts).
    let use_key = QueryKey {
        file: FileId(2),
        node: NodeId(4),
        kind: QueryKind::TypeOf,
    };
    let deps = program
        .db
        .cached_deps(&use_key)
        .expect("cross-file use is memoized");
    assert!(deps.contains(&Dep {
        file: FileId(1),
        node: NodeId(0)
    }));
    // Shared-leaf edit: drops the leaf entry plus its one dependent.
    let dropped = program.db.invalidate(Dep {
        file: FileId(1),
        node: NodeId(0),
    });
    assert_eq!(dropped, 2, "shared edit drops exactly own + dependent");
    // Unrelated entries survive: utils LIMIT and main `n`.
    assert!(
        program
            .db
            .cached_deps(&QueryKey {
                file: FileId(0),
                node: NodeId(0),
                kind: QueryKind::TypeOf,
            })
            .is_some(),
        "unrelated leaf survives"
    );
    assert!(
        program
            .db
            .cached_deps(&QueryKey {
                file: FileId(2),
                node: NodeId(0),
                kind: QueryKind::TypeOf,
            })
            .is_some(),
        "unrelated same-file entry survives"
    );
}

/// Leaf edit on a fresh defu-shaped program: exactly one entry drops.
#[test]
fn defu_graph_leaf_edit_invalidates_exactly_one_entry() {
    let mut program = run_program(&[
        FileSpec {
            path: "checked-utils.ts",
            source: include_str!("../../../corpus/check-multifile/checked-utils.ts"),
            objects: &[],
        },
        FileSpec {
            path: "checked-types.ts",
            source: include_str!("../../../corpus/check-multifile/checked-types.ts"),
            objects: &[],
        },
        FileSpec {
            path: "checked-main.ts",
            source: include_str!("../../../corpus/check-multifile/checked-main.ts"),
            objects: &[ObjectSpec {
                name: "p",
                members: &[
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::Number),
                ],
            }],
        },
    ]);
    // Main's `n` (const index 0) is imported by nobody: editing it drops
    // exactly its own entry.
    let dropped = program.db.invalidate(Dep {
        file: FileId(2),
        node: NodeId(0),
    });
    assert_eq!(dropped, 1, "leaf edit drops exactly its own entry");
}

/// Type-only imports decline instead of diagnosing (PITH-P022): a failing
/// `import type` may name a member the target exports only as a type through
/// shapes the subset cannot spell — `PITH2305`/`PITH2307`/`PITH2304` there
/// would risk false verdicts where tsc stays clean (pinned divergence: tsc
/// is silent for existing aliases and `TS2305`/`TS2307` for missing ones).
/// Value imports keep the exact mirrors (pinned by the missing-module tests
/// above).
#[test]
fn type_only_import_declines_instead_of_diagnosing() {
    let program = run_program(&[
        FileSpec {
            path: "t.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "m.ts",
            source: "import type { NOPE } from \"./t\";\n\
                      import type { X } from \"./does-not-exist\";\n\
                      const a: NOPE = 1;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert!(
        main.diagnostics.is_empty(),
        "no false PITH2305/PITH2307/PITH2304: {:?}",
        main.diagnostics
    );
    // Two import declines (missing member, unresolvable specifier) plus one
    // annotation-use decline for `a`.
    assert_eq!(main.unsupported.len(), 3, "reasons: {:?}", main.unsupported);
    assert!(
        main.unsupported
            .iter()
            .all(|note| note.reason.contains("type-only import")),
        "reasons: {:?}",
        main.unsupported
    );
}

/// `import type` of an existing alias checks through expansion (PITH-P035):
/// `export type Alias` records a local-export fact plus an alias fact, so the
/// import resolves and the annotation expands to the target spelling — the
/// P022 decline converts to a check (defu #9). tsc is silent for the clean
/// use and `TS2322` for the wrong one; the solver mirrors both exactly.
#[test]
fn type_alias_import_expands_and_checks() {
    let program = run_program(&[
        FileSpec {
            path: "t.ts",
            source: "export type Alias = number;\n",
            objects: &[],
        },
        FileSpec {
            path: "m.ts",
            source: "import type { Alias } from \"./t\";\n\
                      const a: Alias = 1;\n\
                      const b: Alias = \"oops\";\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert_eq!(
        main.diagnostics.len(),
        1,
        "one PITH2322: {:?}",
        main.diagnostics
    );
    assert_eq!(main.diagnostics[0].code, "PITH2322");
    assert_eq!(
        main.diagnostics[0].message,
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(
        main.unsupported.is_empty(),
        "expansion checks: {:?}",
        main.unsupported
    );
}

/// Re-exported interfaces check through chains (PITH-P035): the `iface-*`
/// corpus case differentials against the recorded tsc baselines (one
/// `TS2322` at the wrong member, one `TS2741` spelling the re-exported
/// interface).
#[test]
fn reexported_interface_matches_baselines() {
    let program = run_program(&[
        FileSpec {
            path: "iface-shared.ts",
            source: include_str!("../../../corpus/check-multifile/iface-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "iface-mid.ts",
            source: include_str!("../../../corpus/check-multifile/iface-mid.ts"),
            objects: &[],
        },
        FileSpec {
            path: "iface-main.ts",
            source: include_str!("../../../corpus/check-multifile/iface-main.ts"),
            objects: &[
                ObjectSpec {
                    name: "ok",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                },
                ObjectSpec {
                    name: "wrong",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::String),
                    ],
                },
                ObjectSpec {
                    name: "missing",
                    members: &[("x", ObjectMemberKind::Number)],
                },
            ],
        },
    ]);
    expect_case(
        "iface",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/iface-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/iface-mid.expected.txt"),
                0,
            ),
            (
                FileId(2),
                include_str!("../../../corpus/check-multifile/iface-main.expected.txt"),
                0,
            ),
        ],
    );
}

/// Re-exported aliases expand transitively (PITH-P035, chains via P052):
/// the `alias-*` corpus case differentials against the recorded tsc
/// baselines (the interface alias checks through the underlying shape,
/// the primitive alias behaves exactly like its target spelling).
#[test]
fn reexported_alias_matches_baselines() {
    let program = run_program(&[
        FileSpec {
            path: "alias-shared.ts",
            source: include_str!("../../../corpus/check-multifile/alias-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "alias-mid.ts",
            source: include_str!("../../../corpus/check-multifile/alias-mid.ts"),
            objects: &[],
        },
        FileSpec {
            path: "alias-main.ts",
            source: include_str!("../../../corpus/check-multifile/alias-main.ts"),
            objects: &[
                ObjectSpec {
                    name: "ok",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                },
                ObjectSpec {
                    name: "wrong",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::String),
                    ],
                },
            ],
        },
    ]);
    expect_case(
        "alias",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/alias-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/alias-mid.expected.txt"),
                0,
            ),
            (
                FileId(2),
                include_str!("../../../corpus/check-multifile/alias-main.expected.txt"),
                0,
            ),
        ],
    );
}

/// Star barrels re-export type members transparently (PITH-P035): the
/// `typestar-*` corpus case differentials against the recorded tsc baseline.
#[test]
fn star_barrel_type_matches_baselines() {
    let program = run_program(&[
        FileSpec {
            path: "typestar-shared.ts",
            source: include_str!("../../../corpus/check-multifile/typestar-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "typestar-index.ts",
            source: include_str!("../../../corpus/check-multifile/typestar-index.ts"),
            objects: &[],
        },
        FileSpec {
            path: "typestar-main.ts",
            source: include_str!("../../../corpus/check-multifile/typestar-main.ts"),
            objects: &[
                ObjectSpec {
                    name: "ok",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                },
                ObjectSpec {
                    name: "wrong",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::String),
                    ],
                },
            ],
        },
    ]);
    expect_case(
        "typestar",
        &program,
        &[
            (
                FileId(0),
                include_str!("../../../corpus/check-multifile/typestar-shared.expected.txt"),
                0,
            ),
            (
                FileId(1),
                include_str!("../../../corpus/check-multifile/typestar-index.expected.txt"),
                0,
            ),
            (
                FileId(2),
                include_str!("../../../corpus/check-multifile/typestar-main.expected.txt"),
                0,
            ),
        ],
    );
}

/// Cyclic type re-exports decline (PITH-P035): the `typecyc-*` corpus files
/// run through the pipeline for explicit assertions (never differentially —
/// the oracle's `TS2303` errors land on the re-export statements, the pinned
/// gap). The cycle declines at the import and the annotation stays
/// uncheckable; the links themselves carry no verdict.
#[test]
fn cyclic_type_reexport_declines() {
    let program = run_program(&[
        FileSpec {
            path: "typecyc-a.ts",
            source: include_str!("../../../corpus/check-multifile/typecyc-a.ts"),
            objects: &[],
        },
        FileSpec {
            path: "typecyc-b.ts",
            source: include_str!("../../../corpus/check-multifile/typecyc-b.ts"),
            objects: &[],
        },
        FileSpec {
            path: "typecyc-main.ts",
            source: include_str!("../../../corpus/check-multifile/typecyc-main.ts"),
            objects: &[],
        },
    ]);
    for file in [FileId(0), FileId(1)] {
        let report = program.report.file(file).expect("link report");
        assert!(
            report.diagnostics.is_empty(),
            "links carry no verdict: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "links carry no decline: {:?}",
            report.unsupported
        );
    }
    let main = program.report.file(FileId(2)).expect("main report");
    assert!(
        main.diagnostics.is_empty(),
        "no false PITH2305 over the cycle: {:?}",
        main.diagnostics
    );
    assert_eq!(main.unsupported.len(), 2, "reasons: {:?}", main.unsupported);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("cycle")),
        "import decline names the cycle: {:?}",
        main.unsupported
    );
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("not an enum or interface")),
        "annotation decline: {:?}",
        main.unsupported
    );
}

/// Unexpandable aliases decline with reasons (PITH-P035, chains via P052):
/// complex (object-literal target) and generic aliases stay outside the
/// subset while the direct alias AND the chained alias check. tsc resolves
/// every one of these; only the complex and generic declines are pinned
/// divergences now (probed 7.0.2).
#[test]
fn chained_alias_resolves_while_complex_and_generic_decline() {
    let program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "export interface Point { x: number; y: number; }\n\
                     export type First = Point;\n\
                     export type Second = First;\n\
                     export type Obj = { x: number };\n\
                     export type Gen<T> = T;\n",
            objects: &[],
        },
        FileSpec {
            path: "mid.ts",
            source: "export { First, Second, Obj, Gen } from \"./shared\";\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { First, Second, Obj, Gen } from \"./mid\";\n\
                      const f: First = { x: 1, y: 2 };\n\
                      const s: Second = { x: 1, y: 2 };\n\
                      const o: Obj = { x: 1 };\n\
                      const g: Gen = 1;\n",
            objects: &[
                ObjectSpec {
                    name: "f",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                },
                ObjectSpec {
                    name: "s",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                },
            ],
        },
    ]);
    let main = program.report.file(FileId(2)).expect("main report");
    assert!(
        main.diagnostics.is_empty(),
        "the chain checks clean, declines never verdict: {:?}",
        main.diagnostics
    );
    assert_eq!(main.unsupported.len(), 2, "reasons: {:?}", main.unsupported);
    for fragment in ["non-identifier alias targets", "generic"] {
        assert!(
            main.unsupported
                .iter()
                .any(|note| note.reason.contains(fragment)),
            "missing '{fragment}': {:?}",
            main.unsupported
        );
    }
}

/// Aliases over imported names resolve transitively (PITH-P035, chains via
/// P052): the target resolves through the declaring file's own import into
/// the next declaring file's shape. tsc resolves it (the old chained
/// decline was a pinned divergence, probed 7.0.2).
#[test]
fn alias_over_import_resolves_transitively() {
    let program = run_program(&[
        FileSpec {
            path: "base.ts",
            source: "export interface Point { x: number; y: number; }\n",
            objects: &[],
        },
        FileSpec {
            path: "mid.ts",
            source: "import { Point } from \"./base\";\n\
                      export type First = Point;\n\
                      export { First };\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { First } from \"./mid\";\nconst f: First = { x: 1, y: 2 };\n",
            objects: &[ObjectSpec {
                name: "f",
                members: &[
                    ("x", ObjectMemberKind::Number),
                    ("y", ObjectMemberKind::Number),
                ],
            }],
        },
    ]);
    let main = program.report.file(FileId(2)).expect("main report");
    assert!(
        main.diagnostics.is_empty(),
        "the import hop checks clean: {:?}",
        main.diagnostics
    );
    assert!(
        main.unsupported.is_empty(),
        "no declines: {:?}",
        main.unsupported
    );
}

/// A wrong member through a cross-file alias chain diagnoses at the member
/// (P052): the chain resolves to the underlying interface and checks exactly
/// like a direct shape import. Probed tsc 7.0.2 (`main-wrong.ts`): one
/// `TS2322` at the member.
#[test]
fn chained_alias_wrong_member_diagnoses_like_direct_import() {
    let program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "export interface Point { x: number; y: number; }\n\
                     export type First = Point;\n\
                     export type Second = First;\n",
            objects: &[],
        },
        FileSpec {
            path: "mid.ts",
            source: "export { First, Second } from \"./shared\";\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { Second } from \"./mid\";\n\
                      const ok: Second = { x: 1, y: 2 };\n\
                      const wrong: Second = { x: 1, y: \"oops\" };\n",
            objects: &[
                ObjectSpec {
                    name: "ok",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::Number),
                    ],
                },
                ObjectSpec {
                    name: "wrong",
                    members: &[
                        ("x", ObjectMemberKind::Number),
                        ("y", ObjectMemberKind::String),
                    ],
                },
            ],
        },
    ]);
    let main = program.report.file(FileId(2)).expect("main report");
    assert_eq!(
        main.diagnostics.len(),
        1,
        "diagnostics: {:?}",
        main.diagnostics
    );
    assert_eq!(main.diagnostics[0].code, "PITH2322");
    assert_eq!(
        main.diagnostics[0].message,
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(
        main.unsupported.is_empty(),
        "no declines: {:?}",
        main.unsupported
    );
}

/// Ambiguous star type re-exports decline like values (PITH-P035): the import
/// declines and the annotation stays uncheckable. tsc diagnoses `TS2308` at
/// the barrel statement instead (pinned gap, probed 7.0.2).
#[test]
fn ambiguous_star_type_declines() {
    let program = run_program(&[
        FileSpec {
            path: "a.ts",
            source: "export interface Dup { x: number; }\n",
            objects: &[],
        },
        FileSpec {
            path: "b.ts",
            source: "export interface Dup { x: string; }\n",
            objects: &[],
        },
        FileSpec {
            path: "index.ts",
            source: "export * from \"./a\";\nexport * from \"./b\";\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { Dup } from \"./index\";\nconst d: Dup = { x: 1 };\n",
            objects: &[ObjectSpec {
                name: "d",
                members: &[("x", ObjectMemberKind::Number)],
            }],
        },
    ]);
    let main = program.report.file(FileId(3)).expect("main report");
    assert!(
        main.diagnostics.is_empty(),
        "declines, never verdicts: {:?}",
        main.diagnostics
    );
    assert_eq!(main.unsupported.len(), 2, "reasons: {:?}", main.unsupported);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("ambiguous")),
        "import decline: {:?}",
        main.unsupported
    );
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("not an enum or interface")),
        "annotation decline: {:?}",
        main.unsupported
    );
}

#[test]
fn program_checking_is_deterministic() {
    let specs = [
        FileSpec {
            path: "error-shared.ts",
            source: include_str!("../../../corpus/check-multifile/error-shared.ts"),
            objects: &[],
        },
        FileSpec {
            path: "error-main.ts",
            source: include_str!("../../../corpus/check-multifile/error-main.ts"),
            objects: &[],
        },
    ];
    let first = run_program(&specs);
    let second = run_program(&specs);
    assert_eq!(first.report, second.report);
    assert_eq!(first.db.cache_len(), second.db.cache_len());
}

/// Cross-file invalidation (the persistent-engine thesis): one shared memo
/// store holds every file's `TypeOf` entries; use-file entries record the
/// declaring occurrence as a [`Dep`], so invalidating the shared declaration
/// drops exactly its own plus its dependents' entries, while a leaf edit
/// drops exactly one.
///
/// Occurrence identity is declaration order (the `check_file` convention);
/// the test authors both sides, and the entry-count assertion below pins the
/// assumption structurally.
#[test]
fn shared_edit_invalidates_exactly_dependents() {
    let specs = [
        FileSpec {
            path: "shared.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { LIMIT } from \"./shared\";\n\
                      const n: number = LIMIT;\n\
                      const m: number = 1;\n",
            objects: &[],
        },
        FileSpec {
            path: "leaf.ts",
            source: "const z: string = \"ok\";\n",
            objects: &[],
        },
    ];
    let mut program = run_program(&specs);
    for (file, report) in &program.report.files {
        assert!(
            report.diagnostics.is_empty(),
            "file {file:?}: {:?}",
            report.diagnostics
        );
        assert!(
            report.unsupported.is_empty(),
            "file {file:?}: {:?}",
            report.unsupported
        );
    }
    // Four memo entries: shared LIMIT, main n + m, leaf z.
    assert_eq!(program.db.cache_len(), 4);
    // The use records the declaring occurrence as a cross-file edge.
    let use_key = QueryKey {
        file: FileId(1),
        node: NodeId(0),
        kind: QueryKind::TypeOf,
    };
    let deps = program
        .db
        .cached_deps(&use_key)
        .expect("use entry is memoized");
    assert!(deps.contains(&Dep {
        file: FileId(0),
        node: NodeId(0)
    }));
    // Shared edit: drops the shared entry plus its one dependent.
    let dropped = program.db.invalidate(Dep {
        file: FileId(0),
        node: NodeId(0),
    });
    assert_eq!(dropped, 2, "shared edit drops exactly own + dependent");
    assert_eq!(program.db.cache_len(), 2);
    // Survivors: main m (self-dep only) and leaf z.
    assert!(
        program
            .db
            .cached_deps(&QueryKey {
                file: FileId(1),
                node: NodeId(1),
                kind: QueryKind::TypeOf,
            })
            .is_some(),
        "unrelated same-file entry survives"
    );
    assert!(
        program
            .db
            .cached_deps(&QueryKey {
                file: FileId(2),
                node: NodeId(0),
                kind: QueryKind::TypeOf,
            })
            .is_some(),
        "unrelated file survives"
    );
}

/// Leaf edit on a fresh program: exactly one entry drops (the invalidation
/// sizes per edit position the contract asks for: leaf 1/4, shared 2/4).
#[test]
fn leaf_edit_invalidates_exactly_one_entry() {
    let mut program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { LIMIT } from \"./shared\";\n\
                      const n: number = LIMIT;\n\
                      const m: number = 1;\n",
            objects: &[],
        },
        FileSpec {
            path: "leaf.ts",
            source: "const z: string = \"ok\";\n",
            objects: &[],
        },
    ]);
    assert_eq!(program.db.cache_len(), 4);
    let dropped = program.db.invalidate(Dep {
        file: FileId(2),
        node: NodeId(0),
    });
    assert_eq!(dropped, 1, "leaf edit drops exactly its own entry");
    assert_eq!(program.db.cache_len(), 3);
}

#[test]
fn default_import_declines_at_import_and_use() {
    // tsc accepts default imports structurally (`TS1192` only when the
    // target lacks one); the subset never spells them, so both sites
    // decline with reasons instead of a forced verdict.
    let program = run_program(&[
        FileSpec {
            path: "s.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "m.ts",
            source: "import D from \"./s\";\nconst n: number = D;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 2);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("default import")),
        "reasons: {:?}",
        main.unsupported
    );
}

#[test]
fn namespace_import_declines() {
    let program = run_program(&[
        FileSpec {
            path: "s.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "m.ts",
            source: "import * as ns from \"./s\";\nconst n: number = 1;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 1);
    assert!(
        main.unsupported[0].reason.contains("namespace import"),
        "reason: {}",
        main.unsupported[0].reason
    );
}

#[test]
fn ambiguous_star_exports_decline() {
    // tsc excludes conflicting star names (the use then fails `TS2305`);
    // picking one barrel would be speculation, so the subset declines.
    let program = run_program(&[
        FileSpec {
            path: "a.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "b.ts",
            source: "export const LIMIT: number = 20;\n",
            objects: &[],
        },
        FileSpec {
            path: "index.ts",
            source: "export * from \"./a\";\nexport * from \"./b\";\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { LIMIT } from \"./index\";\nconst n: number = LIMIT;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(3)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 2);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("Ambiguous") || note.reason.contains("ambiguous")),
        "reasons: {:?}",
        main.unsupported
    );
}

#[test]
fn reexport_cycle_declines() {
    let program = run_program(&[
        FileSpec {
            path: "a.ts",
            source: "export { X } from \"./b\";\n",
            objects: &[],
        },
        FileSpec {
            path: "b.ts",
            source: "export { X } from \"./a\";\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { X } from \"./a\";\nconst n: number = X;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(2)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 2);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("cycle")),
        "reasons: {:?}",
        main.unsupported
    );
}

#[test]
fn imported_type_used_as_value_declines() {
    // tsc diagnoses `TS2693` here; without value facts the subset declines
    // instead of risking a wrong verdict.
    let program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "export interface Point {\n  x: number;\n}\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { Point } from \"./shared\";\nconst n: number = Point;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 2);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("is a type, used as a value")),
        "reasons: {:?}",
        main.unsupported
    );
}

#[test]
fn non_literal_cross_file_init_declines() {
    let program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "declare const O: number;\nexport const P: number = O;\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { P } from \"./shared\";\nconst n: number = P;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 2);
    assert!(
        main.unsupported
            .iter()
            .any(|note| note.reason.contains("non-literal")),
        "reasons: {:?}",
        main.unsupported
    );
}

#[test]
fn cross_file_return_annotation_declines() {
    // tsc checks the body against the imported type (clean here); the
    // synthetic-const return path cannot spell named types, so it declines
    // instead of inventing `PITH2304`.
    let program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "export interface Point {\n  x: number;\n  y: number;\n}\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { Point } from \"./shared\";\n\
                      function f(): Point {\n  return { x: 1, y: 2 };\n}\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert!(main.diagnostics.is_empty());
    assert_eq!(main.unsupported.len(), 1);
    assert!(
        main.unsupported[0].reason.contains("cross-file type"),
        "reason: {}",
        main.unsupported[0].reason
    );
}

#[test]
fn failed_import_use_reports_only_the_import_diagnostic() {
    // Probed tsc 7.0.2: a use of a failed import adds no second error —
    // only `TS2305` at the import. The solver mirrors that: exactly one
    // diagnostic, and the use falls back to the mechanical non-literal note.
    let program = run_program(&[
        FileSpec {
            path: "shared.ts",
            source: "export const LIMIT: number = 10;\n",
            objects: &[],
        },
        FileSpec {
            path: "main.ts",
            source: "import { NOPE } from \"./shared\";\nconst n: number = NOPE;\n",
            objects: &[],
        },
    ]);
    let main = program.report.file(FileId(1)).expect("main report");
    assert_eq!(main.diagnostics.len(), 1);
    assert_eq!(main.diagnostics[0].code, CODE_NO_EXPORTED);
    assert_eq!(main.unsupported.len(), 1);
}

#[test]
fn missing_module_use_reports_only_ts2307() {
    let program = run_program(&[FileSpec {
        path: "main.ts",
        source: "import { X } from \"./does-not-exist\";\nconst n: number = X;\n",
        objects: &[],
    }]);
    let main = program.report.file(FileId(0)).expect("main report");
    assert_eq!(main.diagnostics.len(), 1);
    assert_eq!(main.diagnostics[0].code, CODE_NO_MODULE);
    assert_eq!(main.unsupported.len(), 1);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: declaration fields, sliced identifier
    // names, literal spellings, and import facts verbatim from the adapter;
    // only the enum translations are driver-side.
    let source = "import { LIMIT } from \"./s\";\n\
                  const n: number = LIMIT;\n\
                  const m: number = 2;\n";
    let parsed = parse_module(FileId(0), "m.ts", source);
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    let binder = build_binder_multi(std::slice::from_ref(&parsed));
    let (consts, idents, texts) = consts_from_facts(&parsed, &binder, source, &[]);
    assert_eq!(consts.len(), 2);
    assert_eq!(consts[0].name, "n");
    assert_eq!(consts[0].annotation.as_deref(), Some("number"));
    assert_eq!(consts[0].init, Some(InitKind::NonLiteral));
    assert_eq!(idents, [Some("LIMIT".to_owned()), None]);
    assert_eq!(texts, [None, Some("2".to_owned())]);
    assert_eq!(consts[1].init, Some(InitKind::Number));
    let (uses, module) = imports_from_facts(&parsed);
    assert_eq!(uses.len(), 1);
    assert_eq!(uses[0].local, "LIMIT");
    assert_eq!(uses[0].imported, ImportedName::Named("LIMIT".to_owned()));
    assert_eq!(uses[0].specifier, "./s");
    assert_eq!(uses[0].span.file, FileId(0));
    assert!(uses[0].imported_span.is_some());
    assert!(uses[0].specifier_span.lo < uses[0].specifier_span.hi);
    let id = binder
        .resolve(FileId(0), uses[0].scope, "LIMIT")
        .expect("import binding resolves");
    assert_eq!(binder.store().get(id).expect("interned").name, "LIMIT");
    assert_eq!(module.file, FileId(0));
    assert_eq!(module.path, String::new());
    assert_eq!(module.local_exports.len(), 0);
    assert!(module.reexports.is_empty());
    assert_eq!(parsed.local_exports.len(), 0);
    assert!(parsed.reexports.is_empty());
}
