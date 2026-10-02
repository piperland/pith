//! Fact-anchored, shape-hand-fed solver end-to-end (PITH-P012): object subset.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] (real
//! scopes + symbols) -> [`decls_from_handfed`] -> [`check_file_with_aliases`] ->
//! [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Division of labor: names, scopes, and spans come from adapter facts (each
//! hand-fed entry must name a real bound symbol); only SHAPES are hand-fed
//! (annotation text, member facts, `let` kinds). Rationale: the adapter
//! emits no `ObjectMemberFact`s and no `let` `DeclFact`s yet — the same
//! hand-fed seam as M1's `compute` closures and the solver's documented
//! BLOCKER — so shapes ride per-fixture tables until the adapter emits
//! them. Spans resolve scope-sensitively through the binder, exactly like
//! the check-const driver.
//!
//! Differential rule: same as check-const — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322`/`TS2741`/`TS2739`/`TS2353` <-> `PITH*`) plus the
//! unsupported count for out-of-subset fixtures.

use pith_frontend::{parse_module, ParsedFile};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_file_with_aliases, ConstDecl, DeclKind, FileReport, InitKind, ObjectInit,
    ObjectMemberInit, ObjectMemberKind, TypeAliasShape,
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

/// One hand-fed shape: everything the adapter cannot emit yet.
///
/// `members: None` means "no object initializer"; `Some(&[])` means an
/// empty `{}` literal. Names must be unique per fixture file so the fact
/// lookup below is unambiguous.
struct HandFed<'a> {
    name: &'a str,
    kind: DeclKind,
    annotation: Option<&'a str>,
    init: Option<InitKind>,
    members: Option<&'a [(&'a str, ObjectMemberKind)]>,
}

/// The shape-hand-fed driver: spans/scopes/identities from adapter facts,
/// shapes from the per-fixture [`HandFed`] table.
fn decls_from_handfed(
    parsed: &ParsedFile,
    binder: &Binder,
    specs: &[HandFed<'_>],
) -> Vec<ConstDecl> {
    specs
        .iter()
        .map(|spec| {
            let name = spec.name;
            let symbol = parsed
                .symbols
                .iter()
                .find(|symbol| symbol.name == name)
                .unwrap_or_else(|| panic!("hand-fed name '{name}' binds nothing"));
            let scope = symbol.scope;
            let id: Option<SymbolId> = binder.resolve(parsed.file, scope, &symbol.name);
            let span: Span = id
                .and_then(|id| binder.store().get(id))
                .map_or(symbol.span, |found| found.span);
            ConstDecl {
                name: symbol.name.clone(),
                span,
                scope,
                symbol: id,
                kind: spec.kind,
                annotation: spec.annotation.map(str::to_owned),
                init: spec.init,
                init_object: spec.members.map(|members| ObjectInit {
                    members: members
                        .iter()
                        .map(|(name, kind)| ObjectMemberInit {
                            name: (*name).to_owned(),
                            kind: *kind,
                        })
                        .collect(),
                    fresh: true,
                }),
                // No array-member facts yet (see the check-functions driver).
                init_array: None,
                cast: None,
            }
        })
        .collect()
}

/// Maps every [`ParsedFile::aliases`] fact onto a [`TypeAliasShape`]
/// (mechanical name + target copy; no object fixture declares one, so this
/// rides empty — the mapping exists so alias-annotated fixtures check like
/// their targets the day one lands here).
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

/// Runs the pipeline on one fixture source with its hand-fed shape table.
fn run_pipeline(source: &str, specs: &[HandFed<'_>]) -> FileReport {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = decls_from_handfed(&parsed, &binder, specs);
    let aliases = aliases_from_facts(&parsed);
    let mut db = QueryDb::new();
    check_file_with_aliases(FILE, &decls, &binder, &mut db, &aliases)
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
fn expect_differential(
    name: &str,
    source: &str,
    specs: &[HandFed<'_>],
    expected: &str,
    unsupported: usize,
) {
    let report = run_pipeline(source, specs);
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

use ObjectMemberKind::{Boolean, Null, Number, Undefined};

#[test]
fn object_correct_is_silent() {
    expect_differential(
        "object_correct_is_silent",
        include_str!("../../../corpus/check-object/object-correct.ts"),
        &[
            HandFed {
                name: "point",
                kind: DeclKind::Const,
                annotation: Some("{ x: number; label: string }"),
                init: None,
                members: Some(&[("x", Number), ("label", ObjectMemberKind::String)]),
            },
            HandFed {
                name: "flags",
                kind: DeclKind::Const,
                annotation: Some("{ done: boolean; nully: null; undef: undefined }"),
                init: None,
                members: Some(&[
                    ("done", Boolean(false)),
                    ("nully", Null),
                    ("undef", Undefined),
                ]),
            },
            HandFed {
                name: "movable",
                kind: DeclKind::Let,
                annotation: Some("{ x: number }"),
                init: None,
                members: Some(&[("x", Number)]),
            },
        ],
        include_str!("../../../corpus/check-object/object-correct.expected.txt"),
        0,
    );
}

#[test]
fn object_missing_member_matches_ts2741() {
    expect_differential(
        "object_missing_member_matches_ts2741",
        include_str!("../../../corpus/check-object/object-missing-member.ts"),
        &[HandFed {
            name: "user",
            kind: DeclKind::Const,
            annotation: Some("{ name: string; age: number }"),
            init: None,
            members: Some(&[("name", ObjectMemberKind::String)]),
        }],
        include_str!("../../../corpus/check-object/object-missing-member.expected.txt"),
        0,
    );
}

#[test]
fn object_missing_many_matches_ts2739() {
    expect_differential(
        "object_missing_many_matches_ts2739",
        include_str!("../../../corpus/check-object/object-missing-many.ts"),
        &[HandFed {
            name: "config",
            kind: DeclKind::Const,
            annotation: Some("{ host: string; port: number; secure: boolean; retries: number }"),
            init: None,
            members: Some(&[
                ("secure", Boolean(false)),
                ("host", ObjectMemberKind::String),
            ]),
        }],
        include_str!("../../../corpus/check-object/object-missing-many.expected.txt"),
        0,
    );
}

#[test]
fn object_wrong_member_matches_ts2322() {
    expect_differential(
        "object_wrong_member_matches_ts2322",
        include_str!("../../../corpus/check-object/object-wrong-member.ts"),
        &[
            HandFed {
                name: "point",
                kind: DeclKind::Const,
                annotation: Some("{ x: number; label: string }"),
                init: None,
                members: Some(&[
                    ("x", ObjectMemberKind::String),
                    ("label", ObjectMemberKind::String),
                ]),
            },
            HandFed {
                name: "count",
                kind: DeclKind::Let,
                annotation: Some("{ total: number }"),
                init: None,
                members: Some(&[("total", Boolean(true))]),
            },
            HandFed {
                name: "crossPrimitive",
                kind: DeclKind::Const,
                annotation: Some("number"),
                init: None,
                members: Some(&[("a", Number)]),
            },
            HandFed {
                name: "crossObject",
                kind: DeclKind::Const,
                annotation: Some("{ a: number }"),
                init: Some(InitKind::Number),
                members: None,
            },
        ],
        include_str!("../../../corpus/check-object/object-wrong-member.expected.txt"),
        0,
    );
}

#[test]
fn object_excess_member_matches_ts2353() {
    expect_differential(
        "object_excess_member_matches_ts2353",
        include_str!("../../../corpus/check-object/object-excess-member.ts"),
        &[HandFed {
            name: "point",
            kind: DeclKind::Const,
            annotation: Some("{ x: number }"),
            init: None,
            members: Some(&[("x", Number), ("extra", ObjectMemberKind::String)]),
        }],
        include_str!("../../../corpus/check-object/object-excess-member.expected.txt"),
        0,
    );
}

#[test]
fn object_error_priority_matches_oracle() {
    expect_differential(
        "object_error_priority_matches_oracle",
        include_str!("../../../corpus/check-object/object-error-priority.ts"),
        &[
            HandFed {
                name: "wrongBeatsExcess",
                kind: DeclKind::Const,
                annotation: Some("{ x: number }"),
                init: None,
                members: Some(&[("x", ObjectMemberKind::String), ("extra", Number)]),
            },
            HandFed {
                name: "excessBeatsMissing",
                kind: DeclKind::Const,
                annotation: Some("{ x: number; y: string }"),
                init: None,
                members: Some(&[("x", Number), ("extra", Number)]),
            },
        ],
        include_str!("../../../corpus/check-object/object-error-priority.expected.txt"),
        0,
    );
}

#[test]
fn object_out_of_subset_is_unsupported() {
    expect_differential(
        "object_out_of_subset_is_unsupported",
        include_str!("../../../corpus/check-object/object-out-of-subset.ts"),
        &[
            HandFed {
                name: "uni",
                kind: DeclKind::Const,
                annotation: Some("{ a: number | string }"),
                init: None,
                members: Some(&[("a", Number)]),
            },
            HandFed {
                name: "bare",
                kind: DeclKind::Const,
                annotation: None,
                init: None,
                members: Some(&[("a", Number)]),
            },
            HandFed {
                name: "source",
                kind: DeclKind::Const,
                annotation: None,
                init: None,
                members: Some(&[("a", Number)]),
            },
            HandFed {
                name: "alias",
                kind: DeclKind::Const,
                annotation: Some("{ a: number }"),
                init: Some(InitKind::NonLiteral),
                members: None,
            },
        ],
        include_str!("../../../corpus/check-object/object-out-of-subset.expected.txt"),
        4,
    );
}

#[test]
fn object_nested_shape_still_declines_while_optional_is_silent() {
    // Nested object member types stay declined (one note); the
    // `{ a?: number } = {}` declarator went silent under PITH-P037 — an
    // absent optional member checks clean in tsc, so silence matches.
    expect_differential(
        "object_nested_annotation_is_unsupported",
        include_str!("../../../corpus/check-object/object-nested-annotation.ts"),
        &[
            HandFed {
                name: "nested",
                kind: DeclKind::Const,
                annotation: Some("{ inner: { x: number } }"),
                init: None,
                members: Some(&[("inner", pith_solver::ObjectMemberKind::NonLiteral)]),
            },
            HandFed {
                name: "maybe",
                kind: DeclKind::Const,
                annotation: Some("{ a?: number }"),
                init: None,
                members: Some(&[]),
            },
        ],
        include_str!("../../../corpus/check-object/object-nested-annotation.expected.txt"),
        1,
    );
}

#[test]
fn object_optional_absent_is_silent() {
    expect_differential(
        "object_optional_absent_is_silent",
        include_str!("../../../corpus/check-object/object-optional-absent.ts"),
        &[HandFed {
            name: "o",
            kind: DeclKind::Const,
            annotation: Some("{ x: number; y?: number }"),
            init: None,
            members: Some(&[("x", Number)]),
        }],
        include_str!("../../../corpus/check-object/object-optional-absent.expected.txt"),
        0,
    );
}

#[test]
fn object_optional_present_matches_oracle() {
    expect_differential(
        "object_optional_present_matches_oracle",
        include_str!("../../../corpus/check-object/object-optional-present.ts"),
        &[
            HandFed {
                name: "ok",
                kind: DeclKind::Const,
                annotation: Some("{ x: number; y?: number }"),
                init: None,
                members: Some(&[("x", Number), ("y", Number)]),
            },
            HandFed {
                name: "bad",
                kind: DeclKind::Const,
                annotation: Some("{ x: number; y?: number }"),
                init: None,
                members: Some(&[("x", Number), ("y", ObjectMemberKind::String)]),
            },
            HandFed {
                name: "miss",
                kind: DeclKind::Const,
                annotation: Some("{ x: number; y?: number }"),
                init: None,
                members: Some(&[]),
            },
        ],
        include_str!("../../../corpus/check-object/object-optional-present.expected.txt"),
        0,
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-object/object-wrong-member.ts");
    let specs = [
        HandFed {
            name: "point",
            kind: DeclKind::Const,
            annotation: Some("{ x: number; label: string }"),
            init: None,
            members: Some(&[
                ("x", ObjectMemberKind::String),
                ("label", ObjectMemberKind::String),
            ]),
        },
        HandFed {
            name: "count",
            kind: DeclKind::Let,
            annotation: Some("{ total: number }"),
            init: None,
            members: Some(&[("total", Boolean(true))]),
        },
        HandFed {
            name: "crossPrimitive",
            kind: DeclKind::Const,
            annotation: Some("number"),
            init: None,
            members: Some(&[("a", Number)]),
        },
        HandFed {
            name: "crossObject",
            kind: DeclKind::Const,
            annotation: Some("{ a: number }"),
            init: Some(InitKind::Number),
            members: None,
        },
    ];
    let first = run_pipeline(source, &specs);
    let second = run_pipeline(source, &specs);
    assert_eq!(first, second);
}

#[test]
fn driver_anchors_every_hand_fed_name_in_facts() {
    // Guards the hand-fed seam: every driven name binds a real symbol with a
    // real scope and a non-degenerate span.
    let parsed = parse_module(
        FILE,
        "o.ts",
        "const p: { x: number } = { x: 1 };\nlet q = 2;\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    let binder = build_binder(&parsed);
    let specs = [
        HandFed {
            name: "p",
            kind: DeclKind::Const,
            annotation: Some("{ x: number }"),
            init: None,
            members: Some(&[("x", Number)]),
        },
        HandFed {
            name: "q",
            kind: DeclKind::Let,
            annotation: None,
            init: Some(InitKind::Number),
            members: None,
        },
    ];
    let decls = decls_from_handfed(&parsed, &binder, &specs);
    assert_eq!(decls.len(), 2);
    for (decl, spec) in decls.iter().zip(&specs) {
        assert_eq!(decl.name, spec.name);
        assert_eq!(decl.span.file, FILE);
        assert!(decl.span.lo < decl.span.hi);
        assert!(decl.symbol.is_some());
    }
}
