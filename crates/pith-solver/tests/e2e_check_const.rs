//! Fact-fed solver end-to-end (PITH-P011): the first true pipeline verdict.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`decls_from_facts`] (the driver: [`DeclFact`](pith_frontend::DeclFact)
//! to [`ConstDecl`], plus the P048 seam — bare-identifier initializer names
//! sliced mechanically from init fact spans, asserted in
//! `driver_maps_facts_without_hand_feeding`) -> [`check_file_with_aliases`] ->
//! [`FileReport`],
//! then a differential against the recorded tsc `.expected.txt` baselines.
//!
//! Driver placement rationale: this integration test IS the driver. A
//! `src/driver` module would either add a runtime `pith-frontend` dependency
//! (a layering inversion: Oxc-tainted facts flowing into the solver API) or
//! be `cfg(test)`-gated anyway, gaining nothing over `tests/`. The
//! dev-dependency mirrors `pith-symbols`' existing test-only frontend
//! adaptation, so the boundary law holds and `check_file` core is untouched.
//!
//! Differential rule: oracle lines are `file:TSNNNN: message`; spans are
//! intentionally discarded (line/col shift with comment edits, per the oracle
//! harness). Comparison is on sorted `(numeric-code, message)` multisets —
//! `TS2322` <-> `PITH2322`, `TS2304` <-> `PITH2304` — plus the unsupported
//! count for out-of-subset fixtures.
//!
//! Scope-sensitivity (P012): the driver resolves every fallback span
//! scope-sensitively (`DeclFact.symbol` -> `SymbolFact.scope` ->
//! [`Binder::resolve`] -> store span) AND threads that scope plus the
//! resolved [`SymbolId`] into each [`ConstDecl`], so `check_file`'s internal
//! span resolution agrees with the driver even when two same-name decls
//! share a file. No check-const fixture shadows a name; the shadowing proof
//! lives in the solver unit tests (`shadowed_same_name_verdicts_against_own_scopes`).
//!
//! Ternary `c ? A : B` initializers (P051): the driver maps the adapter's
//! conditional facts (arm kinds plus arm spans, bare-identifier arm names
//! sliced from arm spans like the P048 seam) into [`ConstDecl::init_ternary`].
//! Agreeing arms check as one literal; differing arms diagnose the
//! rank-ordered union once (`ternary-wrong-then`, `ternary-wrong-else`,
//! `ternary-both-wrong`); nested, complex, and fresh-mix arms decline with
//! distinct reasons (`ternary-nested-declined`,
//! `ternary-complex-arm-declined`, `ternary-fresh-mix-declined`); `any`
//! silences, `unknown` absorbs, `never` vanishes, identifiers resolve, and
//! any condition qualifies (`ternary-call-cond`).

use pith_frontend::{
    parse_module, InitKind as FrontendInitKind, ParsedFile, ReturnKind as FrontendReturnKind,
    TernaryArmFact as FrontendTernaryArm, TernaryFact as FrontendTernary,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_file_with_aliases, ConstDecl, DeclKind, FileReport, InitKind, TernaryArm, TernaryInit,
    TypeAliasShape,
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

/// Maps one frontend ternary-arm kind to the solver's, variant by variant.
///
/// The boolean payload is dropped (the const join spells widened names
/// only — fresh-literal mixes decline solver-side instead of mis-spelling).
/// Exhaustive so a new frontend variant fails to compile instead of
/// silently mis-checking.
fn map_ternary_kind(kind: FrontendReturnKind) -> InitKind {
    match kind {
        FrontendReturnKind::Number => InitKind::Number,
        FrontendReturnKind::String => InitKind::String,
        FrontendReturnKind::Boolean(_) => InitKind::Boolean,
        FrontendReturnKind::Null => InitKind::Null,
        FrontendReturnKind::Undefined => InitKind::Undefined,
        FrontendReturnKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend ternary arm to the solver's (P051): kind through the
/// widened map, span verbatim from facts, the nested flag verbatim, and the
/// P048 seam for bare-identifier arms (driver-sliced from the arm fact span
/// — the adapter emits no identifier facts for arms; anything else feeds
/// `None` and declines solver-side).
fn map_ternary_arm(source: &str, arm: &FrontendTernaryArm) -> TernaryArm {
    let kind = map_ternary_kind(arm.kind);
    let init_ident = if kind == InitKind::NonLiteral && !arm.is_conditional {
        slice_of(source, arm.span)
            .filter(|text| is_bare_identifier(text))
            .map(str::to_owned)
    } else {
        None
    };
    TernaryArm {
        kind,
        span: arm.span,
        init_ident,
        is_conditional: arm.is_conditional,
    }
}

/// Maps one frontend ternary fact to the solver's: both arms in source
/// order, each through [`map_ternary_arm`].
fn map_ternary(source: &str, ternary: &FrontendTernary) -> TernaryInit {
    TernaryInit {
        then_arm: map_ternary_arm(source, &ternary.then_arm),
        else_arm: map_ternary_arm(source, &ternary.else_arm),
    }
}

/// Scope-sensitive fallback span for one declarator: `decl.symbol` indexes
/// `ParsedFile.symbols`, and the `(scope, name)` pair resolves through the
/// binder to the exact declaration span plus its [`SymbolId`]. The scope
/// comes from the new [`DeclFact`](pith_frontend::DeclFact) scope fact;
/// spans fall back to the binding span only when the binder cannot resolve
/// (never happens for well-formed facts).
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
/// recovery from parse errors; mirrors the multifile driver's seam).
fn slice_of(source: &str, span: Span) -> Option<&str> {
    let lo = usize::try_from(span.lo).ok()?;
    let hi = usize::try_from(span.hi).ok()?;
    source.get(lo..hi)
}

/// Whether sliced text is a bare identifier (mirrors the multifile
/// driver's check).
fn is_bare_identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// The fact-fed driver: every [`ConstDecl`] field comes from adapter facts.
///
/// - `name` via `ParsedFile.symbols[decl.symbol]` (never re-typed);
/// - `scope`/`symbol` via the declarator scope fact plus binder resolution;
/// - `kind` is `const` (the adapter emits no `let` facts yet);
/// - `annotation` as the frontend's colon-stripped text verbatim;
/// - `init` via the explicit [`map_init`] variant map;
/// - `init_ident` is the P048 seam: bare-identifier initializer names are
///   driver-sliced from the init fact span (the adapter emits no
///   identifier-init facts — see the solver's module-level BLOCKER);
///   anything else feeds `None` and keeps its historical gate;
/// - `init_object` is `None` (no `ObjectMemberFact`s yet; check-const
///   fixtures hold no object literals anyway).
fn decls_from_facts(parsed: &ParsedFile, binder: &Binder, source: &str) -> Vec<ConstDecl> {
    parsed
        .decls
        .iter()
        .map(|decl| {
            let (name, span, symbol) = fallback_span(parsed, binder, decl.symbol, decl.scope);
            let init_ident = match &decl.init {
                Some(init) if init.kind == FrontendInitKind::NonLiteral => {
                    slice_of(source, init.span)
                        .filter(|text| is_bare_identifier(text))
                        .map(str::to_owned)
                }
                _ => None,
            };
            ConstDecl {
                name,
                span,
                scope: decl.scope,
                symbol,
                kind: DeclKind::Const,
                annotation: decl.annotation.as_ref().map(|ann| ann.text.clone()),
                init: decl.init.as_ref().map(|init| map_init(init.kind)),
                init_ident,
                init_object: None,
                // No array-member facts yet (see the check-functions driver).
                init_array: None,
                cast: None,
                // Ternary arms ride the adapter's conditional facts (P051);
                // the bare-identifier arm seam lives in `map_ternary_arm`.
                init_ternary: decl
                    .init
                    .as_ref()
                    .and_then(|init| init.ternary.as_ref())
                    .map(|ternary| map_ternary(source, ternary)),
            }
        })
        .collect()
}

/// Maps every [`ParsedFile::aliases`] fact onto a [`TypeAliasShape`]
/// (mechanical name + target copy; binding spans stay frontend-side —
/// decline reasons anchor at use sites).
fn aliases_from_facts(parsed: &ParsedFile) -> Vec<TypeAliasShape> {
    parsed
        .aliases
        .iter()
        .map(|fact| TypeAliasShape {
            name: fact.name.clone(),
            target: fact.target_text.clone(),
            has_type_params: fact.has_type_params,
        })
        .collect()
}

/// Runs the full real pipeline on one source text with a fresh binder and db.
fn run_pipeline(source: &str) -> FileReport {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = decls_from_facts(&parsed, &binder, source);
    let aliases = aliases_from_facts(&parsed);
    let mut db = QueryDb::new();
    check_file_with_aliases(FILE, &decls, &binder, &mut db, &aliases)
}

/// Parses normalized oracle lines (`file:TSNNNN: message`) into sorted
/// `(numeric-code, message)` pairs; spans/positions are already folded away.
/// Indented continuation lines (the oracle's union-join elaboration, e.g.
/// the second line of a const-ternary `TS2322`) are SKIPPED, not folded:
/// the solver pins the header line exactly and never emits elaborations,
/// while the oracle harness checks the full text against tsc.
fn parse_baseline(expected: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = expected
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter(|line| !line.starts_with(char::is_whitespace))
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
    let report = run_pipeline(source);
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
                include_str!(concat!("../../../corpus/check-const/", $source)),
                include_str!(concat!("../../../corpus/check-const/", $expected)),
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
    mismatch_number_matches_ts2322,
    "mismatch-number.ts",
    "mismatch-number.expected.txt",
    0
);
fixture_test!(
    mismatch_string_matches_ts2322,
    "mismatch-string.ts",
    "mismatch-string.expected.txt",
    0
);
fixture_test!(
    mismatch_boolean_matches_ts2322,
    "mismatch-boolean.ts",
    "mismatch-boolean.expected.txt",
    0
);
fixture_test!(
    unknown_annotation_matches_ts2304,
    "unknown-annotation.ts",
    "unknown-annotation.expected.txt",
    0
);
fixture_test!(
    multi_declarator_matches_ts2322,
    "multi-declarator.ts",
    "multi-declarator.expected.txt",
    0
);
fixture_test!(
    union_annotation_is_unsupported,
    "union-annotation.ts",
    "union-annotation.expected.txt",
    1
);
fixture_test!(
    no_annotation_is_unsupported,
    "no-annotation.ts",
    "no-annotation.expected.txt",
    1
);
fixture_test!(
    alias_primitive_correct_is_silent,
    "alias-primitive-correct.ts",
    "alias-primitive-correct.expected.txt",
    0
);
fixture_test!(
    alias_primitive_wrong_matches_ts2322,
    "alias-primitive-wrong.ts",
    "alias-primitive-wrong.expected.txt",
    0
);
fixture_test!(
    alias_chained_is_unsupported,
    "alias-chained-declined.ts",
    "alias-chained-declined.expected.txt",
    1
);
fixture_test!(
    alias_shadowed_is_unsupported,
    "alias-shadowed-declined.ts",
    "alias-shadowed-declined.expected.txt",
    1
);
fixture_test!(
    alias_generic_is_unsupported,
    "alias-generic-declined.ts",
    "alias-generic-declined.expected.txt",
    1
);
fixture_test!(
    alias_interface_declines_in_const_entry,
    "alias-interface-declined.ts",
    "alias-interface-declined.expected.txt",
    1
);
fixture_test!(
    ident_chain_checks_like_literals,
    "ident-chain.ts",
    "ident-chain.expected.txt",
    0
);
fixture_test!(
    ternary_clean_is_silent,
    "ternary-clean.ts",
    "ternary-clean.expected.txt",
    0
);
fixture_test!(
    ternary_wrong_then_matches_union_ts2322,
    "ternary-wrong-then.ts",
    "ternary-wrong-then.expected.txt",
    0
);
fixture_test!(
    ternary_wrong_else_matches_union_ts2322,
    "ternary-wrong-else.ts",
    "ternary-wrong-else.expected.txt",
    0
);
fixture_test!(
    ternary_both_wrong_dedupes_to_one_ts2322,
    "ternary-both-wrong.ts",
    "ternary-both-wrong.expected.txt",
    0
);
fixture_test!(
    ternary_ident_arms_are_silent,
    "ternary-ident-clean.ts",
    "ternary-ident-clean.expected.txt",
    0
);
fixture_test!(
    ternary_ident_agreeing_arms_check_as_one_literal,
    "ternary-ident-agree-wrong.ts",
    "ternary-ident-agree-wrong.expected.txt",
    0
);

#[test]
fn ternary_nested_divergence_pins_ts2322() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS2322` with the union spelling on the nested ternary while the
    // solver records one unsupported note and stays silent — the subset
    // joins one level only, never recursively.
    let source = include_str!("../../../corpus/check-const/ternary-nested-declined.ts");
    let expected = include_str!("../../../corpus/check-const/ternary-nested-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string | number' is not assignable to type 'number'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let report = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("nested ternary"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn ternary_fresh_mix_divergence_pins_ts2322() {
    // By design the subset declines where the oracle errors: tsc retains
    // the fresh spelling (`number | "ok"`) on the literal/identifier mix
    // while the solver records one unsupported note and stays silent —
    // widened-only spellings never fake fresh literals (the P034
    // no-misspelling discipline).
    let source = include_str!("../../../corpus/check-const/ternary-fresh-mix-declined.ts");
    let expected =
        include_str!("../../../corpus/check-const/ternary-fresh-mix-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'number | \"ok\"' is not assignable to type 'string'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let report = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("fresh-literal"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

fixture_test!(
    ternary_complex_arm_is_unsupported,
    "ternary-complex-arm-declined.ts",
    "ternary-complex-arm-declined.expected.txt",
    1
);
fixture_test!(
    ternary_any_arm_is_silent,
    "ternary-any-arm-clean.ts",
    "ternary-any-arm-clean.expected.txt",
    0
);
fixture_test!(
    ternary_unknown_arm_absorbs_to_unknown_ts2322,
    "ternary-unknown-arm.ts",
    "ternary-unknown-arm.expected.txt",
    0
);
fixture_test!(
    ternary_call_condition_checks_like_plain,
    "ternary-call-cond.ts",
    "ternary-call-cond.expected.txt",
    0
);

#[test]
fn ident_cycle_declines_with_forward_then_cycle() {
    // Pinned oracle-error divergence (P048): tsc spells TS2448 plus TS2454
    // on the forward use while the solver declines twice — forward, then
    // cycle — with no verdict.
    let source = include_str!("../../../corpus/check-const/ident-cycle-declined.ts");
    let expected = include_str!("../../../corpus/check-const/ident-cycle-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [
            (
                "TS2448".to_owned(),
                "Block-scoped variable 'b' used before its declaration.".to_owned()
            ),
            (
                "TS2454".to_owned(),
                "Variable 'b' is used before being assigned.".to_owned()
            ),
        ],
        "oracle baseline pins the divergence"
    );
    let report = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 2);
    assert!(
        report.unsupported[0]
            .reason
            .contains("used before its declaration"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(
        report.unsupported[1].reason.contains("names it back"),
        "reason: {}",
        report.unsupported[1].reason
    );
}

#[test]
fn ident_depth2_declines_at_second_hop() {
    // Pinned oracle-error divergence (P048): tsc checks through the whole
    // chain (TS2322 on `c`) while single-level propagation stops after
    // `b` — silent plus one unsupported note.
    let source = include_str!("../../../corpus/check-const/ident-depth2-declined.ts");
    let expected = include_str!("../../../corpus/check-const/ident-depth2-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'number' is not assignable to type 'string'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let report = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("single-level"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn ident_let_declines() {
    // Pinned oracle-error divergence (P048): tsc observes the literal
    // through the mutable binding (TS2322) while the solver declines —
    // top-level `let` emits no declarator facts, so the name claims no
    // checkable const.
    let source = include_str!("../../../corpus/check-const/ident-let-declined.ts");
    let expected = include_str!("../../../corpus/check-const/ident-let-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'number' is not assignable to type 'string'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let report = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0]
            .reason
            .contains("no checkable const declarator"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn let_reassignment_still_declines() {
    // Assignments emit no facts, so the single declaration-order pass never
    // observes them: a reassigned `let` declines exactly like an untouched
    // one (tsc errors the ASSIGNMENT itself — probe p07 — while the solver
    // records one note and stays silent).
    let report = run_pipeline("let a = 1;\na = \"s\";\nconst b: number = a;\n");
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0]
            .reason
            .contains("no checkable const declarator"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn undeclared_identifier_use_keeps_historical_decline() {
    // Unresolvable names keep the exact historical gate — resolution adds
    // checks, never new verdicts here.
    let report = run_pipeline("const b: number = nope;\n");
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert_eq!(
        report.unsupported[0].reason,
        "non-literal initializer is outside the subset"
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-const/multi-declarator.ts");
    let first = run_pipeline(source);
    let second = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: names come from symbol linkage, annotation
    // text is verbatim, init kinds map per variant, identifier names slice
    // from the init span, spans anchor to the file.
    let source = "const a: number = 1, b = x;\n";
    let parsed = parse_module(FILE, "m.ts", source);
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.decls.len(), 2);
    let binder = build_binder(&parsed);
    let decls = decls_from_facts(&parsed, &binder, source);
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name, "a");
    assert_eq!(decls[0].annotation.as_deref(), Some("number"));
    assert_eq!(decls[0].init, Some(InitKind::Number));
    assert_eq!(decls[0].init_ident, None);
    assert_eq!(decls[0].kind, DeclKind::Const);
    assert_eq!(decls[0].init_object, None);
    assert!(decls[0].symbol.is_some(), "driver resolves the SymbolId");
    assert_eq!(
        decls[0].scope,
        parsed.symbols[usize::try_from(parsed.decls[0].symbol).expect("dense")].scope
    );
    assert_eq!(decls[1].name, "b");
    assert_eq!(decls[1].annotation, None);
    assert_eq!(decls[1].init, Some(InitKind::NonLiteral));
    assert_eq!(decls[1].init_ident.as_deref(), Some("x"));
    for decl in &decls {
        assert_eq!(decl.span.file, FILE);
        assert!(decl.span.lo < decl.span.hi);
    }
}
