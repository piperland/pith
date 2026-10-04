//! Fact-fed solver end-to-end (PITH-P014): call sites.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`functions_from_facts`] + [`calls_from_facts`] (the drivers:
//! [`FunctionFact`](pith_frontend::FunctionFact) to [`FunctionDecl`] and
//! [`CallFact`](pith_frontend::CallFact) to [`CallSite`], zero hand-feeding)
//! -> [`check_calls`] -> [`FileReport`], then a differential against the
//! recorded tsc `.expected.txt` baselines.
//!
//! Division of labor: declaration names, scopes, spans, parameter facts
//! (names, annotation text, optional/rest markers), and call facts (callee
//! name + identifier span, call span, argument literal kinds + spans) all
//! come from adapter facts. The ONLY driver-side mappings are the
//! literal-kind enum translations (frontend
//! [`CallArgKind`](pith_frontend::CallArgKind) to solver [`InitKind`]),
//! mechanical and exhaustive.
//!
//! Differential rule: same as check-functions — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2554`/`TS2555` <-> `PITH2554`/`PITH2555`, `TS2345` <->
//! `PITH2345`, `TS2769` <-> `PITH2769`, `TS2575` <-> `PITH2575`) plus the
//! unsupported count. Oracle `TS2769` continuation lines (indented, no file
//! prefix) fold into the previous message with `"\n"`, matching the
//! solver's multi-line message. Two fixtures diverge by design (the oracle
//! errors where the subset declines or skips):
//! `unresolved-callee` (oracle `TS2304`, solver silent — the name is already
//! tracked as an unresolved reference, never double-diagnosed) and
//! `required-after-optional-declined` (oracle `TS1016` on the declaration,
//! solver one unsupported — the solver spells no declaration diagnostics).
//! A third pins the generic exclusion: `overload-generic-declined` (oracle
//! `TS2769`, solver one unsupported — generic signatures decline with a
//! distinct reason). Those pin the divergence explicitly instead of forcing
//! a false match. Named (interface/alias) params decline distinctly (P046):
//! `named-param-call-declined` (matching object arg, clean in tsc) records
//! one unsupported note with the opaque reason while the primitive control
//! still diagnoses; `generic-param-declined` pins the legacy `T` decline
//! against a clean oracle. The named scope is driver-collected from the
//! adapter's interface/alias facts (names only — opaque reads nothing
//! else). Overload any-match, union arities, and the gap spelling
//! all match (P044 converted the old `overloads-declined` divergence into
//! a `TS2554` match). Ranges, rest minima, and rest-element checks all
//! match (P037 converted the old `rest-param-declined` divergence into a
//! silent match).

use pith_frontend::{
    parse_module, CallArgKind as FrontendCallArgKind, FunctionBodyFact, ParsedFile,
    ReturnKind as FrontendReturnKind, SingleReturnFact as FrontendReturn,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_solver::{
    check_calls, check_calls_with_named_types, CallArg, CallSite, FileReport, FunctionBody,
    FunctionDecl, FunctionParam, FunctionReturn, InitKind, JoinedReturns, NamedTypeScope,
    ObjectInit, ObjectMemberInit, ObjectMemberKind,
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
        init_object,
        // No array-member facts yet (see the check-functions driver).
        init_array: None,
        cast: None,
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

/// The declaration driver: every [`FunctionDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `params` as names + annotated-ness + annotation text + optional/rest
///   markers verbatim (the call checker's enabling facts);
/// - `return_annotation` as the frontend's colon-stripped text verbatim;
/// - `body` mapped variant by variant, joins faithfully like the
///   check-functions driver (irrelevant to call checking, carried so the
///   decls are complete).
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
                // and P045 else-if chains decline the same way.
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
                has_type_params: !func.type_params.is_empty() || func.type_params_complex,
                return_annotation: func.return_annotation.as_ref().map(|ann| ann.text.clone()),
                body,
            }
        })
        .collect()
}

/// The call-site driver: every [`CallSite`] field comes from adapter facts.
///
/// Callee name plus identifier span, whole-call span, and argument kinds +
/// spans verbatim; only the [`map_call_arg_kind`] enum translation is
/// driver-side.
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

/// Variant pipeline for fixtures where the frontend itself diagnoses (Oxc
/// mirrors tsc diagnostics like TS1016): asserts the expected diagnostic
/// is present instead of asserting silence, then checks facts still flow
/// (Oxc recovers and emits them).
fn run_pipeline_with_frontend_diagnostic(
    source: &str,
    code: &str,
    message: &str,
) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    assert!(
        parsed
            .errors
            .iter()
            .any(|error| error.contains(code) && error.contains(message)),
        "expected frontend {code}: {message}, got: {:?}",
        parsed.errors
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts(&parsed);
    let report = check_calls(FILE, &decls, &calls, &binder);
    (parsed, report)
}

/// Runs the full real pipeline on one source text with a fresh binder.
fn run_pipeline(source: &str) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts(&parsed);
    let report = check_calls(FILE, &decls, &calls, &binder);
    (parsed, report)
}

/// Runs the full real pipeline with the file's named types in scope:
/// interface and alias names driver-collected from the adapter's
/// interface/alias facts (opaque means only names are ever read — no
/// member or target facts flow, mirroring the zero-hand-feeding rule).
fn run_pipeline_named(source: &str) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts(&parsed);
    let mut owned: Vec<String> = parsed
        .interfaces
        .iter()
        .map(|interface| interface.name.clone())
        .collect();
    owned.extend(parsed.aliases.iter().map(|alias| alias.name.clone()));
    let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
    let scope = NamedTypeScope { names: &refs };
    let report = check_calls_with_named_types(FILE, &decls, &calls, &binder, &scope);
    (parsed, report)
}

/// Parses normalized oracle lines (`file:TSNNNN: message`) into sorted
/// `(numeric-code, message)` pairs; spans/positions are already folded away.
/// Indented continuation lines (the oracle's `TS2769` elaboration) fold into
/// the previous message with `"\n"`, matching the solver's multi-line
/// message exactly.
fn parse_baseline(expected: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    for line in expected.lines().filter(|line| !line.trim().is_empty()) {
        if line.starts_with(char::is_whitespace) {
            if let Some(last) = out.last_mut() {
                last.1.push('\n');
                last.1.push_str(line);
            }
            continue;
        }
        let mut parts = line.splitn(3, ':');
        let _file = parts.next().unwrap_or("");
        let code = parts.next().unwrap_or("").trim().to_owned();
        let message = parts.next().unwrap_or("").trim().to_owned();
        out.push((code, message));
    }
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
                include_str!(concat!("../../../corpus/check-calls/", $source)),
                include_str!(concat!("../../../corpus/check-calls/", $expected)),
                $unsupported,
            );
        }
    };
}

fixture_test!(
    correct_calls_are_silent,
    "correct.ts",
    "correct.expected.txt",
    0
);
fixture_test!(
    too_few_matches_ts2554,
    "too-few.ts",
    "too-few.expected.txt",
    0
);
fixture_test!(
    too_many_matches_ts2554,
    "too-many.ts",
    "too-many.expected.txt",
    0
);
fixture_test!(
    wrong_arg_type_matches_ts2345,
    "wrong-arg-type.ts",
    "wrong-arg-type.expected.txt",
    0
);
fixture_test!(
    range_correct_is_silent,
    "range-correct.ts",
    "range-correct.expected.txt",
    0
);
fixture_test!(
    range_too_few_matches_ts2554,
    "range-too-few.ts",
    "range-too-few.expected.txt",
    0
);
fixture_test!(
    range_too_many_matches_ts2554,
    "range-too-many.ts",
    "range-too-many.expected.txt",
    0
);
fixture_test!(
    range_wrong_type_matches_ts2345,
    "range-wrong-type.ts",
    "range-wrong-type.expected.txt",
    0
);
fixture_test!(
    rest_param_admitted_is_silent,
    "rest-param-declined.ts",
    "rest-param-declined.expected.txt",
    0
);
fixture_test!(
    rest_prefix_matches_ts2345_and_ts2555,
    "rest-prefix.ts",
    "rest-prefix.expected.txt",
    0
);
fixture_test!(
    overload_clean_calls_are_silent,
    "overload-clean.ts",
    "overload-clean.expected.txt",
    0
);
fixture_test!(
    overload_first_match_calls_are_silent,
    "overload-first-match.ts",
    "overload-first-match.expected.txt",
    0
);
fixture_test!(
    overload_wrong_all_matches_ts2769,
    "overload-wrong-all.ts",
    "overload-wrong-all.expected.txt",
    0
);
fixture_test!(
    overload_arity_matches_ts2554_and_ts2575,
    "overload-arity.ts",
    "overload-arity.expected.txt",
    0
);

#[test]
fn unresolved_callee_pins_ts2304_and_skips_silently() {
    // By design the subset never double-diagnoses: tsc reports `TS2304`
    // while the solver records nothing — the name is already tracked as an
    // unresolved reference.
    let source = include_str!("../../../corpus/check-calls/unresolved-callee.ts");
    let expected = include_str!("../../../corpus/check-calls/unresolved-callee.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2304".to_owned(),
            "Cannot find name 'missing'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (parsed, report) = run_pipeline(source);
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
    assert_eq!(parsed.calls.len(), 1);
    assert_eq!(parsed.calls[0].callee, "missing");
    assert!(
        parsed
            .unresolved
            .iter()
            .any(|entry| entry.name == "missing"),
        "the skipped callee stays tracked as an unresolved reference"
    );
}

#[test]
fn method_call_excluded_emits_no_facts_and_stays_silent() {
    // Method calls are out of scope: oracle clean on the correctly-aritied
    // call, zero call facts, empty differential on both sides.
    let source = include_str!("../../../corpus/check-calls/method-call-excluded.ts");
    let expected = include_str!("../../../corpus/check-calls/method-call-excluded.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the excluded shape"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        parsed.calls.is_empty(),
        "no call facts for method calls: {:?}",
        parsed.calls
    );
    assert!(report.diagnostics.is_empty());
    assert!(report.unsupported.is_empty());
}

#[test]
fn overloads_resolve_union_arity_to_ts2554() {
    // P044 converted the old decline into a match: both overload signatures
    // admit exactly one argument, so two arguments union to `TS2554`.
    let source = include_str!("../../../corpus/check-calls/overloads-declined.ts");
    let expected = include_str!("../../../corpus/check-calls/overloads-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2554".to_owned(),
            "Expected 1 arguments, but got 2.".to_owned()
        )],
        "oracle baseline pins the union arity"
    );
    expect_differential(
        "overloads_resolve_union_arity_to_ts2554",
        source,
        expected,
        0,
    );
}

#[test]
fn overload_generic_declines_and_pins_ts2769() {
    // Generic signatures decline with a distinct reason: tsc reports
    // `TS2769` (elaborating the last signature) while the solver records one
    // unsupported note — the oracle might match the excluded signature.
    let source = include_str!("../../../corpus/check-calls/overload-generic-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/overload-generic-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2769".to_owned(),
            "No overload matches this call.\n  The last overload gave the following error.\n    \
            Argument of type 'boolean' is not assignable to parameter of type 'number'."
                .to_owned()
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
            .contains("generic type parameters"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn required_after_optional_declines_and_pins_ts1016() {
    // Required-after-optional is outside the subset: tsc errors the
    // declaration (`TS1016`) while the solver declines the call site with
    // one unsupported note.
    let source = include_str!("../../../corpus/check-calls/required-after-optional-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/required-after-optional-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS1016".to_owned(),
            "A required parameter cannot follow an optional parameter.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline_with_frontend_diagnostic(
        source,
        "1016",
        "A required parameter cannot follow an optional parameter.",
    );
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0]
            .reason
            .contains("follows an optional parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn named_param_call_declines_distinctly_and_pins_ts2345() {
    // P046: the `show` call (matching object arg, clean in tsc — probed
    // 7.0.2 `d`) declines distinctly instead of checking, while the
    // primitive control still diagnoses `TS2345`.
    let source = include_str!("../../../corpus/check-calls/named-param-call-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/named-param-call-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2345".to_owned(),
            "Argument of type 'string' is not assignable to parameter of type 'number'.".to_owned()
        )],
        "oracle baseline pins the primitive control"
    );
    let (_, report) = run_pipeline_named(source);
    assert_eq!(report.diagnostics.len(), 1);
    assert_eq!(report.diagnostics[0].code, "PITH2345");
    assert_eq!(
        report.diagnostics[0].message,
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("opaque named type"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert_eq!(report.unsupported[0].file, FILE);
    assert!(report.unsupported[0].span.lo < report.unsupported[0].span.hi);
}

#[test]
fn generic_param_call_declines_as_before_and_pins_clean_oracle() {
    // P046 regression guard: `T` never takes the opaque reason — the call
    // declines with the legacy wording while tsc is clean (probed 7.0.2).
    let source = include_str!("../../../corpus/check-calls/generic-param-declined.ts");
    let expected = include_str!("../../../corpus/check-calls/generic-param-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the generic call"
    );
    let (_, report) = run_pipeline_named(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert_eq!(
        report.unsupported[0].reason,
        "call to 'identity': parameter type 'T' for 'x' is outside the subset"
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-calls/too-many.ts");
    let (_, first) = run_pipeline(source);
    let (_, second) = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: callee names + identifier spans, call
    // spans, argument kinds + spans verbatim from facts; decl params carry
    // annotation text plus optional/rest markers for the checker.
    let parsed = parse_module(
        FILE,
        "m.ts",
        "function add(a: number, b: string): number {\n  return 1;\n}\n\
         function opt(a: number, b?: number): number {\n  return 1;\n}\n\
         add(1, \"ok\");\nobj.pick(1);\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.calls.len(), 1);
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts(&parsed);
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name, "add");
    let texts: Vec<Option<&str>> = decls[0]
        .params
        .iter()
        .map(|param| param.annotation.as_deref())
        .collect();
    assert_eq!(texts, [Some("number"), Some("string")]);
    assert_eq!(decls[1].name, "opt");
    assert!(decls[1].params[1].optional);
    assert_eq!(calls.len(), 1);
    let site = &calls[0];
    assert_eq!(site.callee, "add");
    assert_eq!(site.callee_span.file, FILE);
    assert!(site.callee_span.lo < site.callee_span.hi);
    assert_eq!(site.span.file, FILE);
    assert!(site.span.lo <= site.callee_span.lo);
    assert_eq!(site.callee_span.hi - site.callee_span.lo, 3);
    let kinds: Vec<InitKind> = site.args.iter().map(|arg| arg.kind).collect();
    assert_eq!(kinds, [InitKind::Number, InitKind::String]);
    for arg in &site.args {
        assert_eq!(arg.span.file, FILE);
        assert!(arg.span.lo < arg.span.hi);
    }
}
