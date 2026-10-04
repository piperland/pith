//! Fact-anchored, shape-hand-fed solver end-to-end (PITH-P017): interfaces.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`decls_from_handfed`] + [`shapes_from_facts`] -> [`check_interfaces`] ->
//! [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Division of labor: names, scopes, and spans come from adapter facts
//! (each hand-fed entry must name a real bound symbol; each interface fact
//! must link a real symbol); interface MEMBER shapes come from adapter
//! facts too ([`ParsedFile::interfaces`] — the P017 seam closure), while
//! const-side shapes stay hand-fed (annotation text, member facts, `let`
//! kinds — the same hand-fed seam as M1's `compute` closures and the
//! solver's documented BLOCKER). Spans resolve scope-sensitively through
//! the binder, exactly like the check-object driver.
//!
//! Differential rule: same as check-object — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322`/`TS2741`/`TS2739`/`TS2353` <-> `PITH*`) plus the
//! unsupported count for declined fixtures.

use pith_frontend::{parse_module, ParsedFile};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_interfaces, ConstDecl, DeclKind, FileReport, InitKind, InterfaceHeritage,
    InterfaceMember, InterfaceShape, ObjectInit, ObjectMemberInit, ObjectMemberKind,
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
                init_ident: None,
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
                init_ternary: None,
            }
        })
        .collect()
}

/// The adapter-fed driver: every [`ParsedFile::interfaces`] fact maps
/// mechanically onto an [`InterfaceShape`], with the binder [`SymbolId`]
/// resolved from the checking [`Binder`] — the linkage that makes merged
/// interface+value pairs resolve. Panics on skew (an interface fact that
/// links nothing), like the hand-fed name lookup above.
fn shapes_from_facts(parsed: &ParsedFile, binder: &Binder) -> Vec<InterfaceShape> {
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
    let shapes = shapes_from_facts(&parsed, &binder);
    let mut db = QueryDb::new();
    check_interfaces(FILE, &decls, &shapes, &binder, &mut db)
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
fn iface_correct_is_silent() {
    expect_differential(
        "iface_correct_is_silent",
        include_str!("../../../corpus/check-interfaces/iface-correct.ts"),
        &[
            HandFed {
                name: "point",
                kind: DeclKind::Const,
                annotation: Some("Point"),
                init: None,
                members: Some(&[("x", Number), ("label", ObjectMemberKind::String)]),
            },
            HandFed {
                name: "flags",
                kind: DeclKind::Const,
                annotation: Some("Flags"),
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
                annotation: Some("Point"),
                init: None,
                members: Some(&[("x", Number), ("label", ObjectMemberKind::String)]),
            },
        ],
        include_str!("../../../corpus/check-interfaces/iface-correct.expected.txt"),
        0,
    );
}

#[test]
fn iface_wrong_member_matches_ts2322() {
    expect_differential(
        "iface_wrong_member_matches_ts2322",
        include_str!("../../../corpus/check-interfaces/iface-wrong-member.ts"),
        &[HandFed {
            name: "point",
            kind: DeclKind::Const,
            annotation: Some("Point"),
            init: None,
            members: Some(&[("x", ObjectMemberKind::String), ("label", Number)]),
        }],
        include_str!("../../../corpus/check-interfaces/iface-wrong-member.expected.txt"),
        0,
    );
}

#[test]
fn iface_missing_member_matches_ts2741() {
    expect_differential(
        "iface_missing_member_matches_ts2741",
        include_str!("../../../corpus/check-interfaces/iface-missing-member.ts"),
        &[HandFed {
            name: "user",
            kind: DeclKind::Const,
            annotation: Some("User"),
            init: None,
            members: Some(&[("name", ObjectMemberKind::String)]),
        }],
        include_str!("../../../corpus/check-interfaces/iface-missing-member.expected.txt"),
        0,
    );
}

#[test]
fn iface_excess_member_matches_ts2353() {
    expect_differential(
        "iface_excess_member_matches_ts2353",
        include_str!("../../../corpus/check-interfaces/iface-excess-member.ts"),
        &[HandFed {
            name: "point",
            kind: DeclKind::Const,
            annotation: Some("Point"),
            init: None,
            members: Some(&[("x", Number), ("extra", ObjectMemberKind::String)]),
        }],
        include_str!("../../../corpus/check-interfaces/iface-excess-member.expected.txt"),
        0,
    );
}

#[test]
fn iface_merged_pair_resolves_both_meanings() {
    expect_differential(
        "iface_merged_pair_resolves_both_meanings",
        include_str!("../../../corpus/check-interfaces/iface-merged-pair.ts"),
        &[
            HandFed {
                name: "Foo",
                kind: DeclKind::Const,
                annotation: None,
                init: Some(InitKind::Number),
                members: None,
            },
            HandFed {
                name: "viaIface",
                kind: DeclKind::Const,
                annotation: Some("Foo"),
                init: None,
                members: Some(&[("a", ObjectMemberKind::String)]),
            },
            HandFed {
                name: "useFoo",
                kind: DeclKind::Const,
                annotation: Some("number"),
                init: Some(InitKind::NonLiteral),
                members: None,
            },
        ],
        include_str!("../../../corpus/check-interfaces/iface-merged-pair.expected.txt"),
        2,
    );
}

#[test]
fn iface_heritage_declines_with_reason() {
    expect_differential(
        "iface_heritage_declines_with_reason",
        include_str!("../../../corpus/check-interfaces/iface-heritage-declined.ts"),
        &[HandFed {
            name: "child",
            kind: DeclKind::Const,
            annotation: Some("Child"),
            init: None,
            members: Some(&[("a", ObjectMemberKind::String), ("b", Number)]),
        }],
        include_str!("../../../corpus/check-interfaces/iface-heritage-declined.expected.txt"),
        1,
    );
}

#[test]
fn iface_methods_declines_with_reasons() {
    expect_differential(
        "iface_methods_declines_with_reasons",
        include_str!("../../../corpus/check-interfaces/iface-methods-declined.ts"),
        &[
            HandFed {
                name: "runner",
                kind: DeclKind::Const,
                annotation: Some("Runner"),
                init: None,
                members: Some(&[("run", ObjectMemberKind::NonLiteral)]),
            },
            HandFed {
                name: "lookup",
                kind: DeclKind::Const,
                annotation: Some("Table"),
                init: None,
                members: Some(&[("a", Number)]),
            },
        ],
        include_str!("../../../corpus/check-interfaces/iface-methods-declined.expected.txt"),
        2,
    );
}

#[test]
fn iface_optional_members_absent_silent_present_checked() {
    // PITH-P037 converted the old per-use decline: absent optional members
    // stay silent while present ones run the shared comparison, so both
    // uses match the clean oracle with zero notes. (The `iface-optional-`
    // fixture name records the history; the verdict is now silent.)
    expect_differential(
        "iface_optional_members_absent_silent_present_checked",
        include_str!("../../../corpus/check-interfaces/iface-optional-declined.ts"),
        &[
            HandFed {
                name: "absent",
                kind: DeclKind::Const,
                annotation: Some("WithOpt"),
                init: None,
                members: Some(&[("a", Number)]),
            },
            HandFed {
                name: "present",
                kind: DeclKind::Const,
                annotation: Some("WithOpt"),
                init: None,
                members: Some(&[("a", Number), ("b", ObjectMemberKind::String)]),
            },
        ],
        include_str!("../../../corpus/check-interfaces/iface-optional-declined.expected.txt"),
        0,
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-interfaces/iface-wrong-member.ts");
    let specs = [HandFed {
        name: "point",
        kind: DeclKind::Const,
        annotation: Some("Point"),
        init: None,
        members: Some(&[("x", ObjectMemberKind::String), ("label", Number)]),
    }];
    let first = run_pipeline(source, &specs);
    let second = run_pipeline(source, &specs);
    assert_eq!(first, second);
}

#[test]
fn driver_anchors_every_name_and_links_merged_interfaces() {
    // Guards both seams: every driven name binds a real symbol with a real
    // scope and a non-degenerate span, and every interface fact links the
    // same identity the declarators resolve. The merged `Foo` pins
    // first-declaration anchoring: the const's own site is 35..38, but the
    // merged symbol (and the driver span) sits at the interface id 10..13.
    let parsed = parse_module(
        FILE,
        "m.ts",
        "interface Foo { a: string; }\nconst Foo = 42;\nconst v: Foo = { a: \"s\" };\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    let binder = build_binder(&parsed);
    let shapes = shapes_from_facts(&parsed, &binder);
    assert_eq!(shapes.len(), 1);
    let foo_fact = parsed
        .symbols
        .iter()
        .find(|symbol| symbol.name == "Foo")
        .expect("merged Foo fact");
    let merged = binder
        .resolve(FILE, foo_fact.scope, "Foo")
        .expect("merged Foo");
    assert_eq!(shapes[0].symbol, Some(merged));
    assert_eq!(shapes[0].members.len(), 1);
    assert_eq!(shapes[0].members[0].name, "a");
    assert_eq!(
        shapes[0].members[0].annotation_text.as_deref(),
        Some("string")
    );
    assert!(shapes[0].members[0].complex_reason.is_none());
    let specs = [
        HandFed {
            name: "Foo",
            kind: DeclKind::Const,
            annotation: None,
            init: Some(InitKind::Number),
            members: None,
        },
        HandFed {
            name: "v",
            kind: DeclKind::Const,
            annotation: Some("Foo"),
            init: None,
            members: Some(&[("a", ObjectMemberKind::String)]),
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
    let foo = decls
        .iter()
        .find(|decl| decl.name == "Foo")
        .expect("Foo decl");
    assert_eq!((foo.span.lo, foo.span.hi), (10, 13));
    assert_eq!(foo.symbol, Some(merged));
}
