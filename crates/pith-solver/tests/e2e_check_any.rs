//! Fact-fed solver end-to-end (PITH-P025): `any`/`unknown` boundary plus
//! `as` / `satisfies` / angle assertions.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`decls_from_facts`] / [`functions_from_facts`] + [`calls_from_facts`]
//! (the drivers, zero hand-feeding) -> [`check_file`] / [`check_functions`]
//! / [`check_calls`] -> [`FileReport`], then a differential against the
//! recorded tsc `.expected.txt` baselines.
//!
//! Division of labor: declaration names, scopes, spans, annotation texts,
//! initializer/argument/return literal kinds, and assertion facts (operand
//! kind, target text, operand span, form) all come from adapter facts. The
//! ONLY driver-side mappings are the literal-kind enum translations
//! (frontend kinds to solver [`InitKind`], frontend [`CastKind`] to solver
//! [`CastKind`]) plus echoing `""` for unsliceable cast targets (which the
//! solver declines as complex), mechanical and exhaustive.
//!
//! Differential rule: oracle lines are `file:TSNNNN: message`, compared as
//! sorted `(numeric-code, message)` multisets (`TS`/`PITH` prefixes folded)
//! plus the unsupported count. Two fixtures diverge by design (the oracle
//! errors or stays clean where the subset declines): `unknown-unguarded`
//! (oracle `TS2322`, solver two unsupported — identifier-held `unknown`
//! carries no value-type facts) and `destr-transform` (oracle clean,
//! solver two unsupported — a non-literal return and a non-literal cast
//! operand). Those pin the divergence explicitly instead of forcing a
//! false match.
//!
//! Disclosed seams (same hand-fed class as M1 `compute` closures):
//!
//! - `init_object` is always `None`: no check-any fixture holds an object
//!   literal, so member facts never enter this pipeline.
//! - Which checker runs is per fixture: const fixtures run [`check_file`],
//!   return fixtures run [`check_functions`], call fixtures run
//!   [`check_calls`], and `as-cast-decline` merges [`check_file`] plus
//!   [`check_calls`] (sorted concat — both reports are already sorted, and
//!   the merge re-sorts by `(file, span.lo, span.hi)`).
//! - Casts under named-interface/enum annotations never reach these
//!   checkers (the drivers route everything through the three entry
//!   points above); such positions decline as non-literal inits elsewhere.

use pith_frontend::{
    parse_module, CallArgKind as FrontendCallArgKind, CastFact as FrontendCastFact,
    CastKind as FrontendCastKind, CastOperandKind as FrontendCastOperandKind, FunctionBodyFact,
    InitKind as FrontendInitKind, ParsedFile, ReturnKind as FrontendReturnKind,
    SingleReturnFact as FrontendReturn,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_calls, check_file, check_functions, CallArg, CallSite, CastInput, CastKind, ConstDecl,
    DeclKind, FileReport, FunctionBody, FunctionDecl, FunctionParam, FunctionReturn, InitKind,
    JoinedReturns, ObjectInit, ObjectMemberInit, ObjectMemberKind,
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

/// Maps one frontend initializer kind to the solver's, variant by variant.
///
/// Both enums carry the same six shapes; the match is exhaustive so a new
/// frontend variant fails to compile here instead of silently mis-checking.
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
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
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

/// Maps one frontend call-argument kind to the solver's primitive kind.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
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

/// Maps one frontend cast-operand kind to the solver's primitive kind.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
fn map_cast_operand_kind(kind: FrontendCastOperandKind) -> InitKind {
    match kind {
        FrontendCastOperandKind::Number => InitKind::Number,
        FrontendCastOperandKind::String => InitKind::String,
        FrontendCastOperandKind::Boolean => InitKind::Boolean,
        FrontendCastOperandKind::Null => InitKind::Null,
        FrontendCastOperandKind::Undefined => InitKind::Undefined,
        FrontendCastOperandKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend assertion form to the solver's, variant by variant.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
fn map_cast_kind(kind: FrontendCastKind) -> CastKind {
    match kind {
        FrontendCastKind::As => CastKind::As,
        FrontendCastKind::Satisfies => CastKind::Satisfies,
        FrontendCastKind::Angle => CastKind::Angle,
    }
}

/// Maps one frontend cast fact to the solver's input.
///
/// An unsliceable target (only possible with recovery from parse errors)
/// echoes as `""`, which the solver declines as complex — recorded, never
/// mis-checked or dropped.
fn map_cast(cast: &FrontendCastFact) -> CastInput {
    CastInput {
        operand: map_cast_operand_kind(cast.operand_kind),
        target: cast.target_text.clone().unwrap_or_default(),
        operand_span: cast.operand_span,
        kind: map_cast_kind(cast.kind),
    }
}

/// Scope-sensitive span + identity for one declarator, mirroring the
/// check-const driver's fallback: `symbol` indexes
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

/// The const driver: every [`ConstDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `kind` is `const` (the adapter emits no `let` facts);
/// - `annotation` as the frontend's colon-stripped text verbatim;
/// - `init` via the explicit [`map_init`] variant map;
/// - `init_object` is `None` (no check-any fixture holds an object
///   literal — disclosed seam);
/// - `cast` via the explicit [`map_cast`] fact map.
fn decls_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<ConstDecl> {
    parsed
        .decls
        .iter()
        .map(|decl| {
            let (name, span, symbol) = fallback_span(parsed, binder, decl.symbol, decl.scope);
            ConstDecl {
                name,
                span,
                scope: decl.scope,
                symbol,
                kind: DeclKind::Const,
                annotation: decl.annotation.as_ref().map(|ann| ann.text.clone()),
                init: decl.init.as_ref().map(|init| map_init(init.kind)),
                init_object: None,
                cast: decl
                    .init
                    .as_ref()
                    .and_then(|init| init.cast.as_ref())
                    .map(map_cast),
            }
        })
        .collect()
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

/// Maps one frontend return expression to the solver's return shape.
///
/// Object returns become member facts (always fresh: only direct syntactic
/// literals carry them); assertion returns carry their cast fact through.
/// Every other return becomes its literal kind.
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
        cast: ret.cast.as_ref().map(map_cast),
    }
}

/// Maps one joined frontend return pair to the solver's joined shape.
fn map_joined(first: &FrontendReturn, second: &FrontendReturn) -> JoinedReturns {
    JoinedReturns {
        first: map_function_return(first),
        second: map_function_return(second),
    }
}

/// The declaration driver: every [`FunctionDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `params` as names + annotated-ness + annotation text + optional/rest
///   markers verbatim;
/// - `return_annotation` as the frontend's colon-stripped text verbatim;
/// - `body` mapped variant by variant (object returns carry member facts,
///   assertion returns carry casts, both via [`map_function_return`]).
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
                        annotation: param.annotation_text.clone(),
                        optional: param.optional,
                        is_rest: param.is_rest,
                    })
                    .collect(),
                params_complex: func.params_complex,
                return_annotation: func.return_annotation.as_ref().map(|ann| ann.text.clone()),
                body,
            }
        })
        .collect()
}

/// The call-site driver: every [`CallSite`] field comes from adapter facts.
///
/// Callee name plus identifier span, whole-call span, and argument kinds +
/// spans verbatim; arguments carry casts via [`map_cast`]. Only the enum
/// translations are driver-side.
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
                    cast: arg.cast.as_ref().map(map_cast),
                })
                .collect(),
        })
        .collect()
}

/// Parses one source text with a fresh binder, asserting clean frontend facts.
fn parse_fixture(source: &str) -> (ParsedFile, Binder) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    (parsed, binder)
}

/// Runs the const pipeline on one source text with a fresh binder and db.
fn run_const(source: &str) -> (ParsedFile, FileReport) {
    let (parsed, binder) = parse_fixture(source);
    let decls = decls_from_facts(&parsed, &binder);
    let mut db = QueryDb::new();
    let report = check_file(FILE, &decls, &binder, &mut db);
    (parsed, report)
}

/// Runs the function-return pipeline on one source text.
fn run_functions(source: &str) -> (ParsedFile, FileReport) {
    let (parsed, binder) = parse_fixture(source);
    let decls = functions_from_facts(&parsed, &binder);
    let mut db = QueryDb::new();
    let report = check_functions(FILE, &decls, &binder, &mut db);
    (parsed, report)
}

/// Runs the call-site pipeline on one source text.
fn run_calls(source: &str) -> (ParsedFile, FileReport) {
    let (parsed, binder) = parse_fixture(source);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts(&parsed);
    let report = check_calls(FILE, &decls, &calls, &binder);
    (parsed, report)
}

/// Merges two per-file reports, re-sorting both sinks by
/// `(file, span.lo, span.hi)` so the merged verdict stays deterministic.
fn merge_reports(first: FileReport, second: FileReport) -> FileReport {
    let mut report = FileReport {
        diagnostics: [first.diagnostics, second.diagnostics].concat(),
        unsupported: [first.unsupported, second.unsupported].concat(),
    };
    report.diagnostics.sort_by(|left, right| {
        (left.file, left.span.lo, left.span.hi).cmp(&(right.file, right.span.lo, right.span.hi))
    });
    report.unsupported.sort_by(|left, right| {
        (left.file, left.span.lo, left.span.hi).cmp(&(right.file, right.span.lo, right.span.hi))
    });
    report
}

/// Runs the const plus call-site pipelines and merges their reports.
fn run_const_and_calls(source: &str) -> (ParsedFile, FileReport) {
    let (parsed, const_report) = run_const(source);
    let (_, call_report) = run_calls(source);
    (parsed, merge_reports(const_report, call_report))
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
fn expect_differential(name: &str, report: &FileReport, expected: &str, unsupported: usize) {
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
    ($test:ident, $run:ident, $source:literal, $expected:literal, $unsupported:expr) => {
        #[test]
        fn $test() {
            let source = include_str!(concat!("../../../corpus/check-any/", $source));
            let expected = include_str!(concat!("../../../corpus/check-any/", $expected));
            let (_, report) = $run(source);
            expect_differential(stringify!($test), &report, expected, $unsupported);
        }
    };
}

fixture_test!(
    any_const_correct_is_silent,
    run_const,
    "any-const-correct.ts",
    "any-const-correct.expected.txt",
    0
);

fixture_test!(
    any_param_correct_is_silent,
    run_calls,
    "any-param-correct.ts",
    "any-param-correct.expected.txt",
    0
);

fixture_test!(
    any_param_wrong_reports_non_any_position,
    run_calls,
    "any-param-wrong.ts",
    "any-param-wrong.expected.txt",
    0
);

fixture_test!(
    any_return_is_silent,
    run_functions,
    "any-return.ts",
    "any-return.expected.txt",
    0
);

fixture_test!(
    as_cast_admit_checks_through,
    run_const,
    "as-cast-admit.ts",
    "as-cast-admit.expected.txt",
    0
);

fixture_test!(
    as_cast_decline_reports_both_families,
    run_const_and_calls,
    "as-cast-decline.ts",
    "as-cast-decline.expected.txt",
    0
);

#[test]
fn unknown_unguarded_pins_ts2322_and_declines() {
    // Identifier-held `unknown` carries no value-type facts: tsc reports
    // `TS2322` while the solver records two unsupported notes (the
    // `declare const` itself has no initializer; the use is non-literal).
    let source = include_str!("../../../corpus/check-any/unknown-unguarded.ts");
    let expected = include_str!("../../../corpus/check-any/unknown-unguarded.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'unknown' is not assignable to type 'string'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (parsed, report) = run_const(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 2);
    assert!(
        report.unsupported[0].reason.contains("missing initializer"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(
        report.unsupported[1].reason.contains("non-literal"),
        "reason: {}",
        report.unsupported[1].reason
    );
    assert_eq!(parsed.decls.len(), 2);
}

#[test]
fn destr_transform_pins_clean_oracle_and_declines() {
    // The destr shape (`any` params, non-literal returns, one non-literal
    // cast operand) is clean in tsc while the solver declines each
    // declaration with a recorded reason.
    let source = include_str!("../../../corpus/check-any/destr-transform.ts");
    let expected = include_str!("../../../corpus/check-any/destr-transform.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the destr shape"
    );
    let (parsed, report) = run_functions(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 2);
    assert!(
        report.unsupported[0].reason.contains("non-literal"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(
        report.unsupported[1].reason.contains("operand"),
        "reason: {}",
        report.unsupported[1].reason
    );
    assert_eq!(parsed.functions.len(), 2);
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-any/as-cast-decline.ts");
    let (_, first) = run_const_and_calls(source);
    let (_, second) = run_const_and_calls(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Every solver input arrives through the fact drivers: the admit
    // fixture's declarators link to binder symbols with assertion facts on
    // three of four initializers (the `satisfies` line included).
    let source = include_str!("../../../corpus/check-any/as-cast-admit.ts");
    let (parsed, _) = run_const(source);
    let binder = build_binder(&parsed);
    let decls = decls_from_facts(&parsed, &binder);
    assert_eq!(decls.len(), 4);
    assert_eq!(parsed.decls.len(), 4);
    let casts = decls.iter().filter(|decl| decl.cast.is_some()).count();
    assert_eq!(casts, 4);
    for decl in &decls {
        assert!(decl.symbol.is_some(), "unlinked declarator: {}", decl.name);
    }
}
