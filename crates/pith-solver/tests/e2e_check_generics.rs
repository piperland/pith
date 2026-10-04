//! Fact-fed solver end-to-end (PITH-P016): generic functions.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`generics_from_facts`] + [`calls_from_facts`] (the drivers:
//! [`FunctionFact`](pith_frontend::FunctionFact) to [`GenericDecl`] and
//! [`CallFact`](pith_frontend::CallFact) to [`CallSite`]) -> [`check_generics`]
//! -> [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Division of labor: declaration names, scopes, spans, parameter facts,
//! return annotations, body shapes, type-parameter names plus bound texts
//! and the modifier flag, and call facts (callee name + identifier span,
//! call span, argument literal kinds + spans) all come from adapter facts. The driver-side
//! mappings are the literal-kind enum translations (mechanical and
//! exhaustive) plus ONE disclosed hand-fed seam: explicit type arguments ride
//! per-call (`Some(vec!["number"])` for `id<number>(1)`, `None` for `id(1)`)
//! because the adapter emits no call-type-argument facts. Arity, spans, and
//! inferred bindings still come from facts; only the angle-bracket texts are
//! hand-fed — the same seam shape as the const driver's hand-fed
//! annotations, and it vanishes when the adapter emits the facts.
//!
//! The driver routes only declarations carrying type-parameter facts (a
//! non-empty name list or a set complexity flag); plain functions belong to
//! the check-functions/check-calls pipelines instead (documented routing,
//! never a silent drop).
//!
//! Differential rule: oracle header lines are `file:TSNNNN: message`,
//! compared as sorted `(numeric-code, first-line-message)` multisets
//! (`TS2322`/`TS2345`/`TS2304`/`TS2558`/`TS2344` <-> `PITH*`) plus the
//! unsupported count. Elaboration continuation lines (`'T' could be
//! instantiated …`) fold away exactly like check-narrowing's union
//! elaborations. Eight fixtures diverge by design (oracle clean or erroring
//! where the subset declines or skips); each pins its divergence explicitly
//! instead of forcing a false match.

use pith_frontend::{
    parse_module, CallArgKind as FrontendCallArgKind, FunctionBodyFact, ParsedFile,
    ReturnKind as FrontendReturnKind, SingleReturnFact as FrontendReturn,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_solver::{
    check_generics, CallArg, CallSite, FileReport, FunctionBody, FunctionDecl, FunctionParam,
    FunctionReturn, GenericCall, GenericDecl, InitKind, JoinedReturns, ObjectInit,
    ObjectMemberInit, ObjectMemberKind, TypeParamBound,
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
        // Bare-identifier tails stay `None` here (see the check-functions
        // driver): only guard-effect tails resolve through P048.
        init_ident: None,
        init_object,
        // No array-member facts yet (see the check-functions driver).
        init_array: None,
        cast: None,
        ternary: None,
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

/// The declaration driver: every [`GenericDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `params` as names + annotated-ness + annotation text + optional/rest
///   markers verbatim; `return_annotation` as the colon-stripped text;
/// - `type_params` as declared names verbatim, `constraint`/`default` as
///   the sliced bound texts, plus the modifier complexity flag;
/// - `body` mapped variant by variant, joins faithfully like the
///   check-functions driver (object returns become member facts,
///   always fresh: only direct syntactic literals carry them).
///   Only declarations carrying type-parameter facts route here; plain
///   functions belong to the check-functions/check-calls pipelines.
fn generics_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<GenericDecl> {
    parsed
        .functions
        .iter()
        .filter(|func| !func.type_params.is_empty() || func.type_params_complex)
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
            GenericDecl {
                decl: FunctionDecl {
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
                    // Genericity lives in the enclosing `GenericDecl`, never here.
                    has_type_params: false,
                    return_annotation: func.return_annotation.as_ref().map(|ann| ann.text.clone()),
                    body,
                },
                type_params: func
                    .type_params
                    .iter()
                    .map(|param| param.name.clone())
                    .collect(),
                type_params_complex: func.type_params_complex,
                // Every parameter's bounds verbatim: constraints and
                // defaults compose per parameter solver-side (P036).
                bounds: func
                    .type_params
                    .iter()
                    .map(|param| TypeParamBound {
                        constraint: param.constraint_text.clone(),
                        default: param.default_text.clone(),
                    })
                    .collect(),
            }
        })
        .collect()
}

/// The call-site driver: every [`CallSite`] field comes from adapter facts.
///
/// Callee name plus identifier span, whole-call span, and argument kinds +
/// spans verbatim; only the [`map_call_arg_kind`] enum translation is
/// driver-side. Explicit type arguments are NOT facts (the adapter emits
/// none) — the caller supplies them positionally in `explicit`.
fn calls_from_facts(parsed: &ParsedFile, explicit: &[Option<Vec<String>>]) -> Vec<GenericCall> {
    assert_eq!(
        parsed.calls.len(),
        explicit.len(),
        "explicit type arguments must align one per call fact"
    );
    parsed
        .calls
        .iter()
        .zip(explicit.iter())
        .map(|(call, written)| GenericCall {
            call: CallSite {
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
            },
            explicit_args: written.clone(),
        })
        .collect()
}

/// Runs the full real pipeline on one source text with a fresh binder.
fn run_pipeline(source: &str, explicit: &[Option<Vec<String>>]) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = generics_from_facts(&parsed, &binder);
    let calls = calls_from_facts(&parsed, explicit);
    let report = check_generics(FILE, &decls, &calls, &binder);
    (parsed, report)
}

/// Parses normalized oracle HEADER lines (`file:TSNNNN: message`) into sorted
/// `(numeric-code, message)` pairs, folding away continuation lines (the
/// `'T' could be instantiated …` elaborations the solver mirrors only by
/// first line — see the module docs).
fn parse_baseline(expected: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = expected
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| {
            let mut parts = line.splitn(3, ':');
            let _file = parts.next()?;
            let code = parts.next()?.trim().to_owned();
            let message = parts.next()?.trim().to_owned();
            if code.len() > 2
                && code.starts_with("TS")
                && code[2..].chars().all(|c| c.is_ascii_digit())
            {
                Some((code, message))
            } else {
                None
            }
        })
        .collect();
    out.sort();
    out
}

/// Asserts the pipeline verdict differentially equals the recorded baseline:
/// same `(code-family, first-line-message)` multiset (`TS`/`PITH` prefixes
/// folded) and the expected unsupported count, with sane anchored spans
/// throughout.
fn expect_differential(
    name: &str,
    source: &str,
    expected: &str,
    explicit: &[Option<Vec<String>>],
    unsupported: usize,
) {
    let (_, report) = run_pipeline(source, explicit);
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

/// Builds one explicit type-argument list (`id<number>` -> `args1("number")`).
fn args1(first: &str) -> Vec<String> {
    vec![first.to_owned()]
}

/// Builds a two-element explicit type-argument list
/// (`pair<number, string>` -> `args2("number", "string")`).
fn args2(first: &str, second: &str) -> Vec<String> {
    vec![first.to_owned(), second.to_owned()]
}

/// Builds a three-element explicit type-argument list.
fn args3(first: &str, second: &str, third: &str) -> Vec<String> {
    vec![first.to_owned(), second.to_owned(), third.to_owned()]
}

macro_rules! fixture_test {
    ($test:ident, $source:literal, $expected:literal, $explicit:expr, $unsupported:expr) => {
        #[test]
        fn $test() {
            expect_differential(
                stringify!($test),
                include_str!(concat!("../../../corpus/check-generics/", $source)),
                include_str!(concat!("../../../corpus/check-generics/", $expected)),
                $explicit,
                $unsupported,
            );
        }
    };
}

fixture_test!(
    explicit_correct_binds_silently,
    "explicit-correct.ts",
    "explicit-correct.expected.txt",
    &[Some(args1("number"))],
    1
);
fixture_test!(
    explicit_wrong_matches_ts2345,
    "explicit-wrong.ts",
    "explicit-wrong.expected.txt",
    &[Some(args1("number"))],
    1
);
fixture_test!(
    inferred_correct_binds_silently,
    "inferred-correct.ts",
    "inferred-correct.expected.txt",
    &[None, None],
    1
);
fixture_test!(
    inferred_wrong_matches_ts2322,
    "inferred-wrong.ts",
    "inferred-wrong.expected.txt",
    &[None],
    0
);
fixture_test!(
    constrained_correct_binds_silently,
    "constrained-correct.ts",
    "constrained-correct.expected.txt",
    &[None, Some(args1("string"))],
    1
);
fixture_test!(
    constrained_wrong_matches_oracle,
    "constrained-wrong.ts",
    "constrained-wrong.expected.txt",
    &[None, Some(args1("number"))],
    1
);
fixture_test!(
    defaulted_correct_binds_silently,
    "defaulted-correct.ts",
    "defaulted-correct.expected.txt",
    &[None, Some(args1("string"))],
    1
);
fixture_test!(
    defaulted_override_matches_ts2345,
    "defaulted-inference-override.ts",
    "defaulted-inference-override.expected.txt",
    &[None, Some(args1("string"))],
    1
);

#[test]
fn inference_failure_pins_clean_oracle() {
    // No literal candidate: tsc binds from the identifier's type (clean)
    // while the subset declines with a reason (plus the body note).
    let source = include_str!("../../../corpus/check-generics/inference-failure.ts");
    let expected = include_str!("../../../corpus/check-generics/inference-failure.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean without a literal candidate"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 2);
    assert!(
        report
            .unsupported
            .iter()
            .any(|note| note.reason.contains("cannot infer")),
        "reasons: {:?}",
        report.unsupported
    );
}

#[test]
fn multi_param_admitted_against_clean_oracle() {
    // Two independent type parameters now admit: oracle clean while the
    // solver checks the call silently (the pass-through body still declines
    // with its own note).
    let source = include_str!("../../../corpus/check-generics/multi-param-declined.ts");
    let expected = include_str!("../../../corpus/check-generics/multi-param-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on multi-parameter calls"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("non-literal return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

fixture_test!(
    pair_correct_binds_silently,
    "pair-correct.ts",
    "pair-correct.expected.txt",
    &[None],
    1
);
fixture_test!(
    pair_wrong_first_matches_ts2345,
    "pair-wrong-first.ts",
    "pair-wrong-first.expected.txt",
    &[None],
    1
);
fixture_test!(
    pair_wrong_second_matches_ts2345,
    "pair-wrong-second.ts",
    "pair-wrong-second.expected.txt",
    &[None],
    1
);
fixture_test!(
    pair_explicit_correct_binds_silently,
    "pair-explicit-correct.ts",
    "pair-explicit-correct.expected.txt",
    &[Some(args2("number", "string"))],
    1
);
fixture_test!(
    pair_explicit_wrong_matches_ts2345,
    "pair-explicit-wrong.ts",
    "pair-explicit-wrong.expected.txt",
    &[Some(args2("number", "string"))],
    1
);
fixture_test!(
    pair_explicit_count_matches_ts2558,
    "pair-explicit-count.ts",
    "pair-explicit-count.expected.txt",
    &[
        Some(args1("number")),
        Some(args3("number", "string", "boolean"))
    ],
    1
);
fixture_test!(
    triple_correct_binds_silently,
    "triple-correct.ts",
    "triple-correct.expected.txt",
    &[None],
    1
);

#[test]
fn pair_inference_failure_pins_clean_oracle() {
    // No literal candidates: tsc binds from the identifiers' types (clean)
    // while the subset declines naming the first uninferrable parameter
    // (plus the body note).
    let source = include_str!("../../../corpus/check-generics/pair-inference-failure.ts");
    let expected =
        include_str!("../../../corpus/check-generics/pair-inference-failure.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean without literal candidates"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 2);
    assert!(
        report
            .unsupported
            .iter()
            .any(|note| note.reason.contains("cannot infer")),
        "reasons: {:?}",
        report.unsupported
    );
}

#[test]
fn constrained_admitted_against_clean_oracle() {
    // A constrained `<T extends string>` now admits on a matching call:
    // oracle clean while the solver checks silently (the pass-through body
    // still declines with its own note).
    let source = include_str!("../../../corpus/check-generics/constrained-declined.ts");
    let expected = include_str!("../../../corpus/check-generics/constrained-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on matching constrained calls"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("non-literal return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn defaulted_admitted_against_clean_oracle() {
    // A defaulted `<T = number>` now admits on a matching call: oracle
    // clean while the solver checks silently (the pass-through body still
    // declines with its own note).
    let source = include_str!("../../../corpus/check-generics/defaulted-declined.ts");
    let expected = include_str!("../../../corpus/check-generics/defaulted-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on matching defaulted calls"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("non-literal return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn union_member_declined_pins_ts2322() {
    // `T` in a union parameter position errors in tsc itself (the body
    // fails) while the subset declines with a reason.
    let source = include_str!("../../../corpus/check-generics/union-member-declined.ts");
    let expected =
        include_str!("../../../corpus/check-generics/union-member-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string | T' is not assignable to type 'T'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("union parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn object_member_declined_pins_ts2322() {
    // `T` in an object return position errors in tsc itself (the body
    // fails) while the subset declines with a reason.
    let source = include_str!("../../../corpus/check-generics/object-member-declined.ts");
    let expected =
        include_str!("../../../corpus/check-generics/object-member-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'T' is not assignable to type '{ v: T; }'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("object return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn keyof_param_declined_pins_ts2322() {
    // `T` under `keyof` errors in tsc itself (the body fails against `T`)
    // while the subset declines with a `keyof` reason.
    let source = include_str!("../../../corpus/check-generics/keyof-param-declined.ts");
    let expected = include_str!("../../../corpus/check-generics/keyof-param-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'keyof T' is not assignable to type 'T'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("keyof parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn conditional_return_declined_pins_ts2322() {
    // A conditional return errors in tsc itself (the literal fails against
    // the conditional) while the subset declines with a reason.
    let source = include_str!("../../../corpus/check-generics/conditional-return-declined.ts");
    let expected =
        include_str!("../../../corpus/check-generics/conditional-return-declined.expected.txt");
    let want = concat!(
        "Type 'number' is not assignable ",
        "to type 'T extends string ? string : number'."
    );
    assert_eq!(
        parse_baseline(expected),
        [("TS2322".to_owned(), want.to_owned())],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("conditional return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn mapped_return_declined_pins_ts2353() {
    // A mapped return errors in tsc itself (`TS2353` on the returned
    // literal) while the subset declines with a reason.
    let source = include_str!("../../../corpus/check-generics/mapped-return-declined.ts");
    let expected =
        include_str!("../../../corpus/check-generics/mapped-return-declined.expected.txt");
    let want = concat!(
        "Object literal may only specify known properties, and 'v' ",
        "does not exist in type '{ [K in keyof T]: T[K]; }'."
    );
    assert_eq!(
        parse_baseline(expected),
        [("TS2353".to_owned(), want.to_owned())],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source, &[None]);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("mapped return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-generics/explicit-wrong.ts");
    let explicit = [Some(args1("number"))];
    let (_, first) = run_pipeline(source, &explicit);
    let (_, second) = run_pipeline(source, &explicit);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: names from symbol linkage, type-parameter
    // names plus constraint/default texts plus the modifier flag verbatim,
    // params/returns verbatim, call facts verbatim — only angle-bracket
    // texts ride the disclosed hand-fed seam.
    let parsed = parse_module(
        FILE,
        "m.ts",
        "function id<T>(x: T): T {\n  return x;\n}\n\
         function idc<T extends string>(x: T): T {\n  return x;\n}\n\
         id(1);\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.functions.len(), 2);
    let binder = build_binder(&parsed);
    let decls = generics_from_facts(&parsed, &binder);
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].type_params, ["T"]);
    assert!(!decls[0].type_params_complex);
    assert_eq!(decls[0].bounds.len(), 1);
    assert_eq!(decls[0].bounds[0].constraint, None);
    assert_eq!(decls[0].bounds[0].default, None);
    assert_eq!(decls[0].decl.return_annotation.as_deref(), Some("T"));
    assert_eq!(decls[1].type_params, ["T"]);
    assert!(!decls[1].type_params_complex);
    assert_eq!(decls[1].bounds.len(), 1);
    assert_eq!(decls[1].bounds[0].constraint.as_deref(), Some("string"));
    assert_eq!(decls[1].bounds[0].default, None);
    for decl in &decls {
        assert_eq!(decl.decl.span.file, FILE);
        assert!(decl.decl.span.lo < decl.decl.span.hi);
    }
    let calls = calls_from_facts(&parsed, &[None]);
    assert_eq!(calls.len(), 1);
    let site = &calls[0].call;
    assert_eq!(site.callee, "id");
    assert_eq!(site.callee_span.file, FILE);
    assert!(site.callee_span.lo < site.callee_span.hi);
    assert_eq!(site.args.len(), 1);
    assert_eq!(site.args[0].kind, InitKind::Number);
    assert!(calls[0].explicit_args.is_none());
}
