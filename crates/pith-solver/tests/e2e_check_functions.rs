//! Fact-fed solver end-to-end (PITH-P013): function declarations.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`functions_from_facts`] (the driver: [`FunctionFact`](pith_frontend::FunctionFact)
//! to [`FunctionDecl`], zero hand-feeding) -> [`check_functions`] ->
//! [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Division of labor: names, scopes, spans, parameter annotated-ness,
//! return annotations, and body shapes (including return-object member
//! facts) all come from adapter facts. The ONLY driver-side mapping is the
//! literal-kind enum translation (frontend [`ReturnKind`](pith_frontend::ReturnKind)
//! to solver [`InitKind`]/[`ObjectMemberKind`]), mechanical and exhaustive
//! like check-const's `map_init`. Returned object literals are always fresh
//! (only direct syntactic literals carry member facts), mirroring the
//! check-object seam's `fresh: true`.
//!
//! Differential rule: same as check-const — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322` <-> `PITH2322`) plus the unsupported count.
//! Two fixtures diverge by design (the oracle errors where the subset
//! declines): `unannotated-param` (oracle `TS7006`) and `branching`
//! (oracle `TS2322` hidden in a branch). Those pin the divergence
//! explicitly — oracle error present, solver silent with one unsupported
//! note — instead of forcing a false match.

use pith_frontend::{parse_module, FunctionBodyFact, ParsedFile, ReturnKind as FrontendReturnKind};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_functions, FileReport, FunctionBody, FunctionDecl, FunctionParam, FunctionReturn,
    InitKind, ObjectInit, ObjectMemberInit, ObjectMemberKind,
};
use pith_symbols::{Binder, ScopeInput, SymbolInput, UnresolvedInput};

const FILE: FileId = FileId(0);

/// Builds a fresh binder from one parsed file's scope/symbol/unresolved facts.
fn build_binder(parsed: &ParsedFile) -> Binder {
    let scopes: Vec<ScopeInput> = parsed
        .scopes
        .iter()
        .map(|scope| ScopeInput {
            index: scope.index,
            parent: scope.parent,
        })
        .collect();
    let symbols: Vec<SymbolInput> = parsed
        .symbols
        .iter()
        .map(|symbol| SymbolInput {
            scope: symbol.scope,
            name: symbol.name.clone(),
            span: symbol.span,
            flags: symbol.flags,
        })
        .collect();
    let unresolved: Vec<UnresolvedInput> = parsed
        .unresolved
        .iter()
        .map(|fact| UnresolvedInput {
            name: fact.name.clone(),
            count: fact.count,
        })
        .collect();
    let mut binder = Binder::new();
    binder.build_file(parsed.file, &scopes, &symbols, &unresolved);
    binder
}

/// Maps one frontend return-literal kind to the solver's primitive kind.
///
/// The boolean payload is dropped here (widened spells); member facts keep
/// it via [`map_member_kind`]. Exhaustive so a new frontend variant fails
/// to compile instead of silently mis-checking.
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

/// Scope-sensitive span + identity for one function declarator, mirroring
/// the check-const driver's fallback: `symbol` indexes
/// `ParsedFile.symbols`, resolved through the binder from the fact's scope.
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

/// The fact-fed driver: every [`FunctionDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `params` as names + annotated-ness verbatim, `params_complex` verbatim;
/// - `return_annotation` as the frontend's colon-stripped text verbatim;
/// - `body` mapped variant by variant; object returns become member facts
///   (always fresh: only direct syntactic literals carry them).
fn functions_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<FunctionDecl> {
    parsed
        .functions
        .iter()
        .map(|func| {
            let (name, span, symbol) = fallback_span(parsed, binder, func.symbol, func.scope);
            let body = match &func.body {
                FunctionBodyFact::SingleReturn(ret) => {
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
                    FunctionBody::SingleReturn(FunctionReturn { kind, init_object })
                }
                FunctionBodyFact::NoBody { declared } => FunctionBody::NoBody {
                    declared: *declared,
                },
                FunctionBodyFact::Empty => FunctionBody::Empty,
                FunctionBodyFact::Complex => FunctionBody::Complex,
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
                    })
                    .collect(),
                params_complex: func.params_complex,
                return_annotation: func.return_annotation.as_ref().map(|ann| ann.text.clone()),
                body,
            }
        })
        .collect()
}

/// Runs the full real pipeline on one source text with a fresh binder and db.
fn run_pipeline(source: &str) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let mut db = QueryDb::new();
    let report = check_functions(FILE, &decls, &binder, &mut db);
    (parsed, report)
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

/// Asserts the pipeline verdict differentially equals the recorded baseline:
/// same `(code-family, message)` multiset (`TS`/`PITH` prefixes folded) and
/// the expected unsupported count, with sane anchored spans throughout.
fn expect_differential(name: &str, source: &str, expected: &str, unsupported: usize) {
    let (_, report) = run_pipeline(source);
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
    let unsupported_notes = &report.unsupported;
    assert_eq!(
        report.unsupported.len(),
        unsupported,
        "{name}: unsupported count: {unsupported_notes:?}"
    );
    for diag in &report.diagnostics {
        assert_eq!(diag.file, FILE, "{name}: diagnostic file");
        assert!(diag.span.lo < diag.span.hi, "{name}: degenerate span");
    }
    for note in &report.unsupported {
        assert_eq!(note.file, FILE, "{name}: unsupported file");
        assert!(note.span.lo < note.span.hi, "{name}: degenerate span");
    }
}

macro_rules! fixture_test {
    ($test:ident, $source:literal, $expected:literal, $unsupported:expr) => {
        #[test]
        fn $test() {
            expect_differential(
                stringify!($test),
                include_str!(concat!("../../../corpus/check-functions/", $source)),
                include_str!(concat!("../../../corpus/check-functions/", $expected)),
                $unsupported,
            );
        }
    };
}

fixture_test!(
    annotated_correct_is_silent,
    "annotated-correct.ts",
    "annotated-correct.expected.txt",
    0
);
fixture_test!(
    return_mismatch_matches_ts2322,
    "return-mismatch.ts",
    "return-mismatch.expected.txt",
    0
);
fixture_test!(
    unannotated_return_is_unsupported,
    "unannotated-return.ts",
    "unannotated-return.expected.txt",
    1
);
fixture_test!(
    multi_return_is_unsupported,
    "multi-return.ts",
    "multi-return.expected.txt",
    1
);
fixture_test!(
    object_return_is_silent,
    "object-return.ts",
    "object-return.expected.txt",
    0
);

#[test]
fn unannotated_param_divergence_pins_ts7006() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS7006` (implicit any under `--strict`) while the solver records one
    // unsupported note and stays silent.
    let source = include_str!("../../../corpus/check-functions/unannotated-param.ts");
    let expected = include_str!("../../../corpus/check-functions/unannotated-param.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS7006".to_owned(),
            "Parameter 'value' implicitly has an 'any' type.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0]
            .reason
            .contains("unannotated parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn branching_divergence_pins_hidden_ts2322() {
    // The flow-phase gap, pinned: tsc reports the `else`-branch mismatch
    // while the straight-line subset declines the whole body.
    let source = include_str!("../../../corpus/check-functions/branching.ts");
    let expected = include_str!("../../../corpus/check-functions/branching.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("complex"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn excluded_shapes_emit_no_facts_and_stay_silent() {
    // Arrows, function expressions, and methods are out of scope: bound
    // symbols, zero function facts, empty differential on both sides.
    let source = include_str!("../../../corpus/check-functions/excluded-shapes.ts");
    let expected = include_str!("../../../corpus/check-functions/excluded-shapes.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on excluded shapes"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        !parsed.symbols.is_empty(),
        "excluded shapes still bind symbols"
    );
    assert!(
        parsed.functions.is_empty(),
        "no function facts for excluded shapes"
    );
    assert!(report.diagnostics.is_empty());
    assert!(report.unsupported.is_empty());
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-functions/return-mismatch.ts");
    let (_, first) = run_pipeline(source);
    let (_, second) = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: names from symbol linkage, params verbatim,
    // annotation text verbatim, return kinds per variant (boolean payload
    // preserved in members), spans anchored to the file.
    let parsed = parse_module(
        FILE,
        "m.ts",
        "function add(a: number, b): string {\n  return \"ok\";\n}\n\
         function point(): { x: number; done: boolean } {\n  return { x: 1, done: false };\n}\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.functions.len(), 2);
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name, "add");
    assert_eq!(decls[0].return_annotation.as_deref(), Some("string"));
    let FunctionBody::SingleReturn(first_return) = &decls[0].body else {
        panic!("expected single return, got {:?}", decls[0].body);
    };
    assert_eq!(first_return.kind, Some(InitKind::String));
    assert!(first_return.init_object.is_none());
    assert!(decls[0].symbol.is_some(), "driver resolves the SymbolId");
    assert_eq!(
        decls[0].scope,
        parsed.symbols[usize::try_from(parsed.functions[0].symbol).expect("dense")].scope
    );
    let param_names: Vec<&str> = decls[0]
        .params
        .iter()
        .map(|param| param.name.as_str())
        .collect();
    assert_eq!(param_names, ["a", "b"]);
    assert_eq!(
        decls[0]
            .params
            .iter()
            .map(|param| param.annotated)
            .collect::<Vec<bool>>(),
        [true, false]
    );
    assert_eq!(decls[1].name, "point");
    for decl in &decls {
        assert_eq!(decl.span.file, FILE);
        assert!(decl.span.lo < decl.span.hi);
    }
    let FunctionBody::SingleReturn(ret) = &decls[1].body else {
        panic!("expected single return, got {:?}", decls[1].body);
    };
    assert_eq!(ret.kind, None);
    let init = ret.init_object.as_ref().expect("object members");
    assert!(init.fresh);
    let members: Vec<(&str, ObjectMemberKind)> = init
        .members
        .iter()
        .map(|member| (member.name.as_str(), member.kind))
        .collect();
    assert_eq!(
        members,
        [
            ("x", ObjectMemberKind::Number),
            ("done", ObjectMemberKind::Boolean(false))
        ]
    );
}
