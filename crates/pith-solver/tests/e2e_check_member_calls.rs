//! Fact-fed solver end-to-end (PITH-P024): member calls on known values.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`member_calls_from_facts`] (the driver:
//! [`MemberCallFact`](pith_frontend::MemberCallFact) to [`MemberCallSite`],
//! zero hand-feeding) -> [`check_member_calls`] -> [`FileReport`], then a
//! differential against the recorded tsc `.expected.txt` baselines.
//!
//! Division of labor: receiver/member names, member spans, call spans, and
//! argument literal kinds + spans all come from adapter facts. The ONLY
//! driver-side mapping is the literal-kind enum translation (frontend
//! [`CallArgKind`](pith_frontend::CallArgKind) to solver [`InitKind`]),
//! mechanical and exhaustive.
//!
//! Differential rule: same as check-calls — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2554` <-> `PITH2554`, `TS2345` <-> `PITH2345`) plus the
//! unsupported count. Three fixtures diverge by design:
//! `member-unknown-member` (oracle `TS2339`, solver one unsupported — full
//! lib types are future work), `member-unknown-receiver` (oracle `TS2304`,
//! solver silent — the name is already tracked as an unresolved reference,
//! never double-diagnosed), and `member-lib-declined` (oracle clean, solver
//! four unsupported — range/overload/variadic lib shapes are outside the
//! opaque subset). Those pin the divergence explicitly instead of forcing a
//! false match.

use pith_frontend::{parse_module, CallArgKind as FrontendCallArgKind, ParsedFile};
use pith_ids::{FileId, Span};
use pith_solver::{check_member_calls, CallArg, FileReport, InitKind, MemberCallSite};
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

/// Maps one frontend member-argument kind to the solver's primitive kind.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
fn map_member_arg_kind(kind: FrontendCallArgKind) -> InitKind {
    match kind {
        FrontendCallArgKind::Number => InitKind::Number,
        FrontendCallArgKind::String => InitKind::String,
        FrontendCallArgKind::Boolean => InitKind::Boolean,
        FrontendCallArgKind::Null => InitKind::Null,
        FrontendCallArgKind::Undefined => InitKind::Undefined,
        FrontendCallArgKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// The member call-site driver: every [`MemberCallSite`] field comes from
/// adapter facts.
///
/// Receiver/member names plus member span, whole-call span, and argument
/// kinds + spans verbatim; only the [`map_member_arg_kind`] enum translation
/// is driver-side.
fn member_calls_from_facts(parsed: &ParsedFile) -> Vec<MemberCallSite> {
    parsed
        .member_calls
        .iter()
        .map(|call| MemberCallSite {
            receiver: call.receiver.clone(),
            member: call.member.clone(),
            member_span: call.member_span,
            span: call.span,
            args: call
                .args
                .iter()
                .map(|arg| CallArg {
                    kind: map_member_arg_kind(arg.kind),
                    span: arg.span,
                    cast: None,
                    // Member-call drivers never feed identifier names.
                    ident: None,
                    // Member-call drivers never feed object members.
                    arg_object: None,
                    // Member-call drivers never feed arrow expressions.
                    arg_arrow: None,
                })
                .collect(),
        })
        .collect()
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
    let calls = member_calls_from_facts(&parsed);
    let report = check_member_calls(FILE, &calls, &binder);
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
                include_str!(concat!("../../../corpus/check-calls/", $source)),
                include_str!(concat!("../../../corpus/check-calls/", $expected)),
                $unsupported,
            );
        }
    };
}

fixture_test!(
    member_correct_calls_are_silent,
    "member-correct.ts",
    "member-correct.expected.txt",
    0
);
fixture_test!(
    member_wrong_type_matches_ts2345,
    "member-wrong-type.ts",
    "member-wrong-type.expected.txt",
    0
);
fixture_test!(
    member_arity_matches_ts2554,
    "member-arity.ts",
    "member-arity.expected.txt",
    0
);

#[test]
fn unknown_member_declines_pins_ts2339() {
    // Full lib types are future work: tsc reports `TS2339` while the solver
    // declines with one unsupported note naming the member.
    let source = include_str!("../../../corpus/check-calls/member-unknown-member.ts");
    let expected = include_str!("../../../corpus/check-calls/member-unknown-member.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2339".to_owned(),
            "Property 'nope' does not exist on type 'JSON'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0]
            .reason
            .contains("unknown member 'nope'"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert_eq!(
        parsed.member_calls.len(),
        1,
        "the declined call still emits a fact"
    );
}

#[test]
fn unknown_receiver_skips_silently_pins_ts2304() {
    // By design the subset never double-diagnoses: tsc reports `TS2304`
    // while the solver records nothing — unknown receivers keep the
    // non-emission, and the name is already tracked as unresolved.
    let source = include_str!("../../../corpus/check-calls/member-unknown-receiver.ts");
    let expected = include_str!("../../../corpus/check-calls/member-unknown-receiver.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [("TS2304".to_owned(), "Cannot find name 'nope'.".to_owned())],
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
    assert!(
        parsed.member_calls.is_empty(),
        "no member facts for unknown receivers: {:?}",
        parsed.member_calls
    );
    assert!(
        parsed.unresolved.iter().any(|entry| entry.name == "nope"),
        "the skipped receiver stays tracked as an unresolved reference"
    );
}

#[test]
fn lib_shapes_declined_against_clean_oracle() {
    // Range arities, overloads, and variadics are outside the opaque subset:
    // oracle clean while the solver declines each site with its lib reason.
    let source = include_str!("../../../corpus/check-calls/member-lib-declined.ts");
    let expected = include_str!("../../../corpus/check-calls/member-lib-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on lib-shaped calls"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(parsed.member_calls.len(), 4);
    assert_eq!(report.unsupported.len(), 4);
    let reasons: Vec<&str> = report
        .unsupported
        .iter()
        .map(|note| note.reason.as_str())
        .collect();
    assert!(
        reasons[0].contains("range of arities"),
        "parse reason: {}",
        reasons[0]
    );
    assert!(
        reasons[1].contains("variadic"),
        "warn reason: {}",
        reasons[1]
    );
    assert!(
        reasons[2].contains("overload"),
        "stringify reason: {}",
        reasons[2]
    );
    assert!(
        reasons[3].contains("variadic"),
        "max reason: {}",
        reasons[3]
    );
}

#[test]
fn non_allowlisted_member_emits_no_facts_and_stays_silent() {
    // Ordinary method calls are out of scope on both sides: oracle clean on
    // the correctly-aritied call, zero member facts, empty differential.
    let source = "const obj = { pick(n: number): number { return n; } };\nobj.pick(1);\n";
    let parsed = parse_module(FILE, "m.ts", source);
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert!(parsed.calls.is_empty());
    assert!(parsed.member_calls.is_empty());
    let binder = build_binder(&parsed);
    let calls = member_calls_from_facts(&parsed);
    let report = check_member_calls(FILE, &calls, &binder);
    assert!(report.diagnostics.is_empty());
    assert!(report.unsupported.is_empty());
}

#[test]
fn untracked_receiver_declines_as_driver_skew() {
    // Unreachable via facts (unknown receivers never emit): a hand-fed site
    // whose receiver is neither allowlisted nor unresolved-tracked declines
    // instead of dropping silently.
    let parsed = parse_module(FILE, "m.ts", "const x: number = 1;\n");
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    let binder = build_binder(&parsed);
    let site = MemberCallSite {
        receiver: "mystery".to_owned(),
        member: "run".to_owned(),
        member_span: Span {
            file: FILE,
            lo: 0,
            hi: 1,
        },
        span: Span {
            file: FILE,
            lo: 0,
            hi: 2,
        },
        args: Vec::new(),
    };
    let report = check_member_calls(FILE, &[site], &binder);
    assert!(report.diagnostics.is_empty());
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0]
            .reason
            .contains("undeclared receiver 'mystery'"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-calls/member-arity.ts");
    let (_, first) = run_pipeline(source);
    let (_, second) = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: receiver/member names plus member span,
    // call span, argument kinds + spans verbatim from facts.
    let parsed = parse_module(FILE, "m.ts", "JSON.parse(\"s\", 1);\nobj.pick(1);\n");
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert!(parsed.calls.is_empty());
    assert_eq!(parsed.member_calls.len(), 1);
    let calls = member_calls_from_facts(&parsed);
    assert_eq!(calls.len(), 1);
    let site = &calls[0];
    assert_eq!(site.receiver, "JSON");
    assert_eq!(site.member, "parse");
    assert_eq!(site.member_span.file, FILE);
    assert_eq!(site.member_span.hi - site.member_span.lo, 5);
    assert_eq!(site.span.file, FILE);
    assert!(site.span.lo <= site.member_span.lo);
    assert!(site.member_span.hi <= site.span.hi);
    let kinds: Vec<InitKind> = site.args.iter().map(|arg| arg.kind).collect();
    assert_eq!(kinds, [InitKind::String, InitKind::Number]);
    for arg in &site.args {
        assert_eq!(arg.span.file, FILE);
        assert!(arg.span.lo < arg.span.hi);
    }
}
