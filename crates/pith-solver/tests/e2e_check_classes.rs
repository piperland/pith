//! Fact-fed solver end-to-end (PITH-P020): classes and `new` expressions.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`classes_from_facts`] + [`news_from_facts`] (the drivers:
//! [`ClassFact`](pith_frontend::ClassFact) to [`ClassDecl`] and
//! [`NewFact`](pith_frontend::NewFact) to [`NewSite`], zero hand-feeding)
//! -> [`check_classes`] -> [`FileReport`], then a differential against the
//! recorded tsc `.expected.txt` baselines.
//!
//! Division of labor: class names, scopes, spans, property facts (names,
//! annotation text, initializer kinds + spans + member facts), constructor
//! parameter facts (names, annotation text, optional/rest markers), family
//! flags, and construction-site facts (class name + identifier span, whole
//! span, argument kinds + spans) all come from adapter facts. The ONLY
//! driver-side mappings are the literal-kind enum translations (frontend
//! [`ClassPropKind`](pith_frontend::ClassPropKind) /
//! [`NewArgKind`](pith_frontend::NewArgKind) to solver [`InitKind`] /
//! [`ObjectMemberKind`]), mechanical and exhaustive.
//!
//! Differential rule: same as check-calls — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322` <-> `PITH2322`, `TS2554` <-> `PITH2554`,
//! `TS2345` <-> `PITH2345`) plus the unsupported count. Four fixtures
//! diverge by design (the oracle errors or stays clean where the subset
//! declines): `methods-declined` and `accessors-declined` (oracle `TS2322`,
//! solver one unsupported — bodies are unchecked), `heritage-declined` and
//! `abstract-declined` (oracle clean, solver one unsupported — heritage and
//! abstract semantics are future work). Those pin the divergence explicitly
//! instead of forcing a false match.

use pith_frontend::{
    parse_module, ClassFamily as FrontendFamily, ClassPropKind as FrontendPropKind,
    NewArgKind as FrontendNewArgKind, ParsedFile,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_classes, CallArg, ClassDecl, ClassFamily, ClassProp, FileReport, FunctionParam, InitKind,
    NewSite, ObjectInit, ObjectMemberInit, ObjectMemberKind,
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

/// Maps one frontend property-value kind to the solver's primitive kind.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking. The boolean payload is dropped: `TS2322` messages spell
/// widened names only (probed 7.0.2).
fn map_prop_kind(kind: FrontendPropKind) -> InitKind {
    match kind {
        FrontendPropKind::Number => InitKind::Number,
        FrontendPropKind::String => InitKind::String,
        FrontendPropKind::Boolean(_) => InitKind::Boolean,
        FrontendPropKind::Null => InitKind::Null,
        FrontendPropKind::Undefined => InitKind::Undefined,
        FrontendPropKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend property-member kind to the solver's member kind,
/// preserving the boolean payload for tsc's fresh-literal spelling.
fn map_member_kind(kind: FrontendPropKind) -> ObjectMemberKind {
    match kind {
        FrontendPropKind::Number => ObjectMemberKind::Number,
        FrontendPropKind::String => ObjectMemberKind::String,
        FrontendPropKind::Boolean(value) => ObjectMemberKind::Boolean(value),
        FrontendPropKind::Null => ObjectMemberKind::Null,
        FrontendPropKind::Undefined => ObjectMemberKind::Undefined,
        FrontendPropKind::NonLiteral => ObjectMemberKind::NonLiteral,
    }
}

/// Maps one frontend construction-argument kind to the solver's kind.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking.
fn map_new_arg_kind(kind: FrontendNewArgKind) -> InitKind {
    match kind {
        FrontendNewArgKind::Number => InitKind::Number,
        FrontendNewArgKind::String => InitKind::String,
        FrontendNewArgKind::Boolean => InitKind::Boolean,
        FrontendNewArgKind::Null => InitKind::Null,
        FrontendNewArgKind::Undefined => InitKind::Undefined,
        FrontendNewArgKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Scope-sensitive span + identity for one class declarator, mirroring the
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

/// The declaration driver: every [`ClassDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `properties` as names + annotation text + initializer kinds/spans (+
///   member facts for `{ ... }` values) verbatim, plus the adapter's decline
///   marker;
/// - `ctor_params` as names + annotated-ness + annotation text +
///   optional/rest markers verbatim (the `new` checker's enabling facts);
/// - every family flag verbatim (the solver declines on them, never on a
///   miscount).
fn classes_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<ClassDecl> {
    parsed
        .classes
        .iter()
        .map(|fact| {
            let (name, span, symbol) = fallback_span(parsed, binder, fact.symbol, fact.scope);
            let properties = fact
                .properties
                .iter()
                .map(|prop| {
                    let (init, init_object) = match prop.init.as_ref() {
                        None => (None, None),
                        Some(init) => match init.members.as_ref() {
                            None => (Some(map_prop_kind(init.kind)), None),
                            Some(members) => (
                                None,
                                Some(ObjectInit {
                                    members: members
                                        .iter()
                                        .map(|member| ObjectMemberInit {
                                            name: member.name.clone(),
                                            kind: map_member_kind(member.kind),
                                        })
                                        .collect(),
                                    fresh: true,
                                }),
                            ),
                        },
                    };
                    ClassProp {
                        name: prop.name.clone(),
                        span: prop.span,
                        annotation: prop.annotation_text.clone(),
                        init,
                        init_object,
                        complex_reason: prop.complex_reason.clone(),
                    }
                })
                .collect();
            ClassDecl {
                name,
                span,
                scope: fact.scope,
                symbol,
                properties,
                ctor_params: fact
                    .ctor_params
                    .iter()
                    .map(|param| FunctionParam {
                        name: param.name.clone(),
                        annotated: param.annotated,
                        annotation: param.annotation_text.clone(),
                        optional: param.optional,
                        is_rest: param.is_rest,
                    })
                    .collect(),
                ctor_complex: fact.ctor_complex,
                ctor_overloads: fact.ctor_overloads,
                declined: fact
                    .declined
                    .iter()
                    .map(|family| map_family(*family))
                    .collect(),
                form: pith_solver::ClassForm {
                    is_expression: fact.form.is_expression,
                    is_abstract: fact.form.is_abstract,
                    is_declare: fact.form.is_declare,
                },
                has_type_params: fact.has_type_params,
            }
        })
        .collect()
}

/// Maps one frontend family flag to the solver's, variant by variant.
///
/// Both enums carry the same eight shapes; the match is exhaustive so a new
/// frontend variant fails to compile here instead of silently mis-checking.
fn map_family(family: FrontendFamily) -> ClassFamily {
    match family {
        FrontendFamily::Methods => ClassFamily::Methods,
        FrontendFamily::Accessors => ClassFamily::Accessors,
        FrontendFamily::Heritage => ClassFamily::Heritage,
        FrontendFamily::Statics => ClassFamily::Statics,
        FrontendFamily::Decorators => ClassFamily::Decorators,
        FrontendFamily::Computed => ClassFamily::Computed,
        FrontendFamily::IndexSignature => ClassFamily::IndexSignature,
        FrontendFamily::ThisAssignments => ClassFamily::ThisAssignments,
    }
}

/// The construction-site driver: every [`NewSite`] field comes from adapter
/// facts.
///
/// Class name plus identifier span, whole-expression span, and argument
/// kinds + spans verbatim; only the [`map_new_arg_kind`] enum translation
/// is driver-side.
fn news_from_facts(parsed: &ParsedFile) -> Vec<NewSite> {
    parsed
        .news
        .iter()
        .map(|site| NewSite {
            class_name: site.class_name.clone(),
            callee_span: site.callee_span,
            span: site.span,
            args: site
                .args
                .iter()
                .map(|arg| CallArg {
                    kind: map_new_arg_kind(arg.kind),
                    span: arg.span,
                    cast: None,
                    // Constructor drivers never feed identifier names.
                    ident: None,
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
    let decls = classes_from_facts(&parsed, &binder);
    let news = news_from_facts(&parsed);
    let mut db = QueryDb::new();
    let report = check_classes(FILE, &decls, &news, &binder, &mut db);
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
                include_str!(concat!("../../../corpus/check-classes/", $source)),
                include_str!(concat!("../../../corpus/check-classes/", $expected)),
                $unsupported,
            );
        }
    };
}

fixture_test!(
    correct_class_is_silent,
    "correct.ts",
    "correct.expected.txt",
    0
);
fixture_test!(
    prop_mismatch_matches_ts2322,
    "prop-mismatch.ts",
    "prop-mismatch.expected.txt",
    0
);
fixture_test!(
    ctor_arity_matches_ts2554,
    "ctor-arity.ts",
    "ctor-arity.expected.txt",
    0
);
fixture_test!(
    new_arg_type_matches_ts2345,
    "new-argtype.ts",
    "new-argtype.expected.txt",
    0
);

#[test]
fn methods_declined_pins_ts2322() {
    // Method bodies are unchecked: tsc reports `TS2322` at the bad return
    // while the solver declines with one class-level note.
    let source = include_str!("../../../corpus/check-classes/methods-declined.ts");
    let expected = include_str!("../../../corpus/check-classes/methods-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
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
        report.unsupported[0].reason.contains("method"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0]
        .declined
        .contains(&pith_frontend::ClassFamily::Methods));
}

#[test]
fn heritage_declined_against_clean_oracle() {
    // Heritage is outside the subset: oracle clean while the solver declines
    // the subclass with one note (the base class stays silent).
    let source = include_str!("../../../corpus/check-classes/heritage-declined.ts");
    let expected = include_str!("../../../corpus/check-classes/heritage-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on plain heritage"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("heritage"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert_eq!(parsed.classes.len(), 2);
    assert!(!parsed.classes[0]
        .declined
        .contains(&pith_frontend::ClassFamily::Heritage));
    assert!(parsed.classes[1]
        .declined
        .contains(&pith_frontend::ClassFamily::Heritage));
}

#[test]
fn accessors_declined_pins_ts2322() {
    // Accessors are unchecked: tsc reports `TS2322` at the bad getter return
    // while the solver declines with one class-level note.
    let source = include_str!("../../../corpus/check-classes/accessors-declined.ts");
    let expected = include_str!("../../../corpus/check-classes/accessors-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
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
        report.unsupported[0].reason.contains("accessor"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0]
        .declined
        .contains(&pith_frontend::ClassFamily::Accessors));
}

#[test]
fn abstract_declined_against_clean_oracle() {
    // Abstract semantics are outside the subset: oracle clean while the
    // solver declines the whole declaration (properties included).
    let source = include_str!("../../../corpus/check-classes/abstract-declined.ts");
    let expected = include_str!("../../../corpus/check-classes/abstract-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on abstract declarations"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("abstract"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0].form.is_abstract);
}

#[test]
fn this_assignments_decline_against_clean_oracle() {
    // `this.x = v` satisfies definite assignment in tsc (clean oracle) but
    // needs flow facts: the solver checks everything else and notes the
    // assignment family once.
    let source = "class C {\nx: number = 0;\nconstructor(v: number) {\nthis.x = v;\n}\n}\n\
                  const c = new C(1);\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("this"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0]
        .declined
        .contains(&pith_frontend::ClassFamily::ThisAssignments));
    assert_eq!(parsed.news.len(), 1);
}

#[test]
fn missing_initializer_pins_ts2564() {
    // Definite assignment (`TS2564` under `--strict`) needs flow facts: the
    // solver declines the property instead of verdicting.
    let source = "class C {\nx: number;\n}\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("missing initializer"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0].properties[0].init.is_none());
}

#[test]
fn declare_class_declines_against_clean_oracle() {
    // Ambient classes never implement anything here: oracle clean while the
    // solver declines the declaration and skips its `new` site silently.
    let source = "declare class C {\nx: number;\nconstructor(a: number);\n}\nconst c = new C(1);\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("declare"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0].form.is_declare);
    assert_eq!(parsed.news.len(), 1);
}

#[test]
fn class_expression_declined_pins_ts2322() {
    // Class expressions record honestly and decline: tsc checks the property
    // (`TS2322`) while the solver notes the expression form.
    let source = "const K = class Named {\nx: number = \"oops\";\n};\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("expression"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0].form.is_expression);
}

#[test]
fn statics_declined_pins_ts2322() {
    // Static-side checking is outside the instance subset: tsc reports
    // `TS2322` on the static prop while the solver notes statics once.
    let source = "class C {\nstatic s: number = \"oops\";\n}\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("static"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0]
        .declined
        .contains(&pith_frontend::ClassFamily::Statics));
    assert!(parsed.classes[0].properties.is_empty());
}

#[test]
fn computed_key_declined_pins_ts2322() {
    // Computed keys cannot feed name-based checking: tsc reports `TS2322`
    // while the solver notes the computed family once.
    let source = "class C {\n[\"k\"]: number = \"oops\";\n}\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("computed"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0]
        .declined
        .contains(&pith_frontend::ClassFamily::Computed));
}

#[test]
fn implicit_ctor_takes_zero_arguments() {
    // No constructor means 0 parameters: oracle `TS2554` matches by
    // construction through the reused call path.
    let source = "class C {\nx: number = 1;\n}\nconst c = new C(1);\n";
    let expected = "implicit.ts:TS2554: Expected 0 arguments, but got 1.\n";
    expect_differential("implicit_ctor_takes_zero_arguments", source, expected, 0);
}

#[test]
fn too_many_new_matches_ts2554() {
    // Excess construction arguments anchor at the first excess argument,
    // mirroring tsc through the reused call path.
    let source = "class C {\nconstructor(a: number) {}\n}\nconst c = new C(1, 2);\n";
    let expected = "many.ts:TS2554: Expected 1 arguments, but got 2.\n";
    expect_differential("too_many_new_matches_ts2554", source, expected, 0);
}

#[test]
fn optional_ctor_param_matches_range_arity() {
    // Range arities flow through the shared call path: oracle `TS2554`
    // matches by construction (PITH-P037 converted the old per-site
    // decline into a verdict).
    let source = "class C {\nconstructor(a: number, b?: number) {}\n}\nconst c = new C(1, 2, 3);\n";
    let expected = "range.ts:TS2554: Expected 1-2 arguments, but got 3.\n";
    expect_differential(
        "optional_ctor_param_matches_range_arity",
        source,
        expected,
        0,
    );
}

#[test]
fn ctor_overloads_decline_news_silently() {
    // Overload resolution is future work: oracle picks an overload (clean)
    // while the solver notes the constructor once and skips the site.
    let source = "class C {\nconstructor(a: number);\nconstructor(a: string);\n\
                  constructor(a: unknown) {}\n}\nconst c = new C(1);\n";
    let (parsed, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("overload"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(parsed.classes[0].ctor_overloads);
    assert_eq!(parsed.news.len(), 1);
}

#[test]
fn unresolved_new_skips_silently() {
    // By design the subset never double-diagnoses: tsc reports `TS2304`
    // (`Cannot find name 'Missing'.`, probed 7.0.2) while the solver records
    // nothing — the name is already tracked as an unresolved reference.
    let source = "const c = new Missing(1);\n";
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
    assert_eq!(parsed.news.len(), 1);
    assert_eq!(parsed.news[0].class_name, "Missing");
    assert!(
        parsed
            .unresolved
            .iter()
            .any(|entry| entry.name == "Missing"),
        "the skipped class stays tracked as an unresolved reference"
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-classes/new-argtype.ts");
    let (_, first) = run_pipeline(source);
    let (_, second) = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: names + spans, property annotation/init
    // facts, ctor param markers, family flags, and construction-site facts
    // verbatim from facts; decl params carry annotation text plus
    // optional/rest markers for the checker.
    let parsed = parse_module(
        FILE,
        "m.ts",
        "class C {\nx: number = 1;\nconstructor(a: number, b?: string) {}\nm(): void {}\n}\n\
         const c = new C(1, \"ok\");\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.classes.len(), 1);
    assert_eq!(parsed.news.len(), 1);
    let binder = build_binder(&parsed);
    let decls = classes_from_facts(&parsed, &binder);
    let news = news_from_facts(&parsed);
    assert_eq!(decls.len(), 1);
    let decl = &decls[0];
    assert_eq!(decl.name, "C");
    assert_eq!(decl.properties.len(), 1);
    assert_eq!(decl.properties[0].name, "x");
    assert_eq!(decl.properties[0].annotation.as_deref(), Some("number"));
    assert_eq!(decl.properties[0].init, Some(InitKind::Number));
    assert_eq!(decl.properties[0].span.file, FILE);
    assert_eq!(decl.ctor_params.len(), 2);
    assert_eq!(decl.ctor_params[0].annotation.as_deref(), Some("number"));
    assert!(decl.ctor_params[1].optional);
    assert!(decl.declined.contains(&ClassFamily::Methods));
    assert!(!decl.declined.contains(&ClassFamily::Heritage));
    assert_eq!(news.len(), 1);
    let site = &news[0];
    assert_eq!(site.class_name, "C");
    assert_eq!(site.callee_span.file, FILE);
    assert!(site.callee_span.lo < site.callee_span.hi);
    assert_eq!(site.span.file, FILE);
    assert!(site.span.lo <= site.callee_span.lo);
    let kinds: Vec<InitKind> = site.args.iter().map(|arg| arg.kind).collect();
    assert_eq!(kinds, [InitKind::Number, InitKind::String]);
    for arg in &site.args {
        assert_eq!(arg.span.file, FILE);
        assert!(arg.span.lo < arg.span.hi);
    }
}
