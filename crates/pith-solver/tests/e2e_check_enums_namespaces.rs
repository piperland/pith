//! Fact-anchored, shape-hand-fed solver end-to-end (PITH-P018): enums +
//! namespaces.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`decls_from_handfed`] + [`shapes_from_facts`] -> [`check_enums`] ->
//! [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Division of labor: names, scopes, and spans come from adapter facts
//! (each hand-fed entry must name a real bound symbol; each enum, interface,
//! and namespace fact must link a real symbol); enum/interface/namespace
//! SHAPES come from adapter facts too (the P018 seam closure), while
//! const-side shapes stay hand-fed (annotation text, member facts, literal
//! texts — the same hand-fed seam as M1's `compute` closures and the
//! solver's documented BLOCKER). Literal spellings ride [`EnumDecl`]'s
//! `init_text`: the driver slices the adapter's own init span and asserts
//! the slice equals the hand-fed text, so the seam is span-grounded, never
//! string-searched. Spans resolve scope-sensitively through the binder,
//! exactly like the check-object driver.
//!
//! Differential rule: same as check-object — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322`/`TS2694`/`TS2709`/`TS2749`/`TS2713`/`TS2741`/`TS2739`/
//! `TS2353` <-> `PITH*`) plus the unsupported count for declined fixtures.
//! The unresolved-head skip (`NS2.Foo`: tsc `TS2503`, solver silent) cannot
//! differential-match by design and gets a dedicated skip test instead.

use pith_frontend::{parse_module, EnumValueKind, ParsedFile};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_enums, ConstDecl, DeclKind, EnumDecl, EnumInput, EnumMember, EnumMemberValue, EnumShape,
    FileReport, InitKind, InterfaceHeritage, InterfaceMember, InterfaceShape, NamespaceShape,
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

/// One hand-fed shape: everything the adapter cannot emit yet.
///
/// `members: None` means "no object initializer"; `Some(&[])` means an
/// empty `{}` literal. `init_text: Some` is required exactly for literal
/// inits (`Number`/`String`/`Boolean`) and must equal the source slice of
/// the adapter's init span (asserted); anything else carries `None`. Names
/// must be unique per fixture file so the fact lookup below is unambiguous.
struct HandFed<'a> {
    name: &'a str,
    kind: DeclKind,
    annotation: Option<&'a str>,
    init: Option<InitKind>,
    members: Option<&'a [(&'a str, ObjectMemberKind)]>,
    init_text: Option<&'a str>,
}

/// The shape-hand-fed driver: spans/scopes/identities from adapter facts,
/// shapes from the per-fixture [`HandFed`] table.
fn decls_from_handfed(
    parsed: &ParsedFile,
    binder: &Binder,
    source: &str,
    specs: &[HandFed<'_>],
) -> Vec<EnumDecl> {
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
            ground_init_text(parsed, source, symbol.index, spec);
            EnumDecl {
                decl: ConstDecl {
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
                },
                init_text: spec.init_text.map(str::to_owned),
                cross_file_deps: Vec::new(),
            }
        })
        .collect()
}

/// Asserts the literal-text seam is span-grounded: literal inits carry the
/// exact source slice of the adapter's init span; every other shape carries
/// no text (those paths never read it).
fn ground_init_text(parsed: &ParsedFile, source: &str, symbol: u32, spec: &HandFed<'_>) {
    let literal = matches!(
        spec.init,
        Some(InitKind::Number | InitKind::String | InitKind::Boolean)
    );
    if !literal {
        assert!(
            spec.init_text.is_none(),
            "non-literal '{}' carries literal text",
            spec.name
        );
        return;
    }
    let text = spec
        .init_text
        .unwrap_or_else(|| panic!("literal '{}' needs init_text", spec.name));
    let fact = parsed
        .decls
        .iter()
        .find(|decl| decl.symbol == symbol)
        .unwrap_or_else(|| panic!("literal '{}' links no decl fact", spec.name));
    let init = fact
        .init
        .as_ref()
        .unwrap_or_else(|| panic!("literal '{}' has no init fact", spec.name));
    let sliced = &source[init.span.lo as usize..init.span.hi as usize];
    assert_eq!(
        sliced, text,
        "init_text for '{}' is not the init span slice",
        spec.name
    );
}

/// The adapter-fed driver: every [`ParsedFile::enums`] fact maps
/// mechanically onto an [`EnumShape`], with the binder [`SymbolId`]
/// resolved from the checking [`Binder`]. Panics on skew (a fact that links
/// nothing), like the hand-fed name lookup above.
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
                        value: match &member.value {
                            EnumValueKind::Number(found) => EnumMemberValue::Number(*found),
                            EnumValueKind::String(found) => EnumMemberValue::String(found.clone()),
                            EnumValueKind::Computed { reason } => EnumMemberValue::Computed {
                                reason: reason.clone(),
                            },
                        },
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

/// The adapter-fed driver: every [`ParsedFile::namespaces`] fact maps
/// mechanically onto a [`NamespaceShape`]. Panics on skew.
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

/// The adapter-fed driver: every [`ParsedFile::interfaces`] fact maps
/// mechanically onto an [`InterfaceShape`]. Panics on skew.
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

/// Runs the pipeline on one fixture source with its hand-fed shape table.
fn run_pipeline(source: &str, specs: &[HandFed<'_>]) -> FileReport {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = decls_from_handfed(&parsed, &binder, source, specs);
    let enums = enums_from_facts(&parsed, &binder);
    let interfaces = interfaces_from_facts(&parsed, &binder);
    let namespaces = namespaces_from_facts(&parsed, &binder);
    let input = EnumInput {
        enums: &enums,
        interfaces: &interfaces,
        namespaces: &namespaces,
    };
    let mut db = QueryDb::new();
    check_enums(FILE, &decls, &input, &binder, &mut db)
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

use ObjectMemberKind::{Boolean, Number};

#[test]
fn enum_numeric_checks_membership_by_value() {
    expect_differential(
        "enum_numeric_checks_membership_by_value",
        include_str!("../../../corpus/check-enums-namespaces/enum-numeric.ts"),
        &[
            HandFed {
                name: "a",
                kind: DeclKind::Const,
                annotation: Some("Color"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
            HandFed {
                name: "b",
                kind: DeclKind::Const,
                annotation: Some("Color"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("5"),
            },
            HandFed {
                name: "c",
                kind: DeclKind::Const,
                annotation: Some("Color"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("2.5"),
            },
            HandFed {
                name: "d",
                kind: DeclKind::Const,
                annotation: Some("Base"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("6"),
            },
            HandFed {
                name: "e",
                kind: DeclKind::Const,
                annotation: Some("Base"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("9"),
            },
            HandFed {
                name: "f",
                kind: DeclKind::Const,
                annotation: Some("Color"),
                init: Some(InitKind::Boolean),
                members: None,
                init_text: Some("true"),
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/enum-numeric.expected.txt"),
        0,
    );
}

#[test]
fn enum_string_literals_never_match() {
    expect_differential(
        "enum_string_literals_never_match",
        include_str!("../../../corpus/check-enums-namespaces/enum-string.ts"),
        &[
            HandFed {
                name: "g",
                kind: DeclKind::Const,
                annotation: Some("Str"),
                init: Some(InitKind::String),
                members: None,
                init_text: Some("\"a\""),
            },
            HandFed {
                name: "h",
                kind: DeclKind::Const,
                annotation: Some("Str"),
                init: Some(InitKind::String),
                members: None,
                init_text: Some("\"z\""),
            },
            HandFed {
                name: "i",
                kind: DeclKind::Const,
                annotation: Some("Str"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
            HandFed {
                name: "j",
                kind: DeclKind::Const,
                annotation: Some("Str"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
            HandFed {
                name: "u",
                kind: DeclKind::Const,
                annotation: Some("Str"),
                init: Some(InitKind::Undefined),
                members: None,
                init_text: None,
            },
            HandFed {
                name: "n",
                kind: DeclKind::Const,
                annotation: Some("Str"),
                init: Some(InitKind::Null),
                members: None,
                init_text: None,
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/enum-string.expected.txt"),
        1,
    );
}

#[test]
fn enum_const_checks_identically() {
    expect_differential(
        "enum_const_checks_identically",
        include_str!("../../../corpus/check-enums-namespaces/enum-const.ts"),
        &[
            HandFed {
                name: "t",
                kind: DeclKind::Const,
                annotation: Some("CE"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("0"),
            },
            HandFed {
                name: "v",
                kind: DeclKind::Const,
                annotation: Some("CE"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("7"),
            },
            HandFed {
                name: "w",
                kind: DeclKind::Const,
                annotation: Some("CE"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/enum-const.expected.txt"),
        1,
    );
}

#[test]
fn enum_computed_declines_with_reason() {
    expect_differential(
        "enum_computed_declines_with_reason",
        include_str!("../../../corpus/check-enums-namespaces/enum-computed-declined.ts"),
        &[
            HandFed {
                name: "p",
                kind: DeclKind::Const,
                annotation: Some("Comp"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("10"),
            },
            HandFed {
                name: "q",
                kind: DeclKind::Const,
                annotation: Some("Comp"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
            HandFed {
                name: "r",
                kind: DeclKind::Const,
                annotation: Some("Comp"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/enum-computed-declined.expected.txt"),
        3,
    );
}

#[test]
fn enum_ambient_declines_with_reason() {
    expect_differential(
        "enum_ambient_declines_with_reason",
        include_str!("../../../corpus/check-enums-namespaces/enum-ambient-declined.ts"),
        &[
            HandFed {
                name: "a1",
                kind: DeclKind::Const,
                annotation: Some("AE"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("0"),
            },
            HandFed {
                name: "a2",
                kind: DeclKind::Const,
                annotation: Some("AE"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/enum-ambient-declined.expected.txt"),
        2,
    );
}

#[test]
fn ns_enum_qualified_checks_with_short_name() {
    expect_differential(
        "ns_enum_qualified_checks_with_short_name",
        include_str!("../../../corpus/check-enums-namespaces/ns-enum.ts"),
        &[
            HandFed {
                name: "w",
                kind: DeclKind::Const,
                annotation: Some("NS.Dir"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("0"),
            },
            HandFed {
                name: "bad",
                kind: DeclKind::Const,
                annotation: Some("NS.Dir"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("9"),
            },
            HandFed {
                name: "z",
                kind: DeclKind::Const,
                annotation: Some("NS.Dir"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
            HandFed {
                name: "y",
                kind: DeclKind::Const,
                annotation: Some("number"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/ns-enum.expected.txt"),
        2,
    );
}

#[test]
fn ns_interface_qualified_keeps_object_families() {
    expect_differential(
        "ns_interface_qualified_keeps_object_families",
        include_str!("../../../corpus/check-enums-namespaces/ns-interface.ts"),
        &[
            HandFed {
                name: "p1",
                kind: DeclKind::Const,
                annotation: Some("NS.Point"),
                init: None,
                members: Some(&[("x", Number)]),
                init_text: None,
            },
            HandFed {
                name: "p2",
                kind: DeclKind::Const,
                annotation: Some("NS.Point"),
                init: None,
                members: Some(&[("x", Number), ("y", ObjectMemberKind::String)]),
                init_text: None,
            },
            HandFed {
                name: "p3",
                kind: DeclKind::Const,
                annotation: Some("NS.Point"),
                init: None,
                members: Some(&[
                    ("x", Number),
                    ("y", ObjectMemberKind::String),
                    ("extra", Boolean(true)),
                ]),
                init_text: None,
            },
            HandFed {
                name: "p4",
                kind: DeclKind::Const,
                annotation: Some("NS.Point"),
                init: None,
                members: Some(&[
                    ("x", ObjectMemberKind::String),
                    ("y", ObjectMemberKind::String),
                ]),
                init_text: None,
            },
            HandFed {
                name: "y",
                kind: DeclKind::Const,
                annotation: Some("number"),
                init: Some(InitKind::NonLiteral),
                members: None,
                init_text: None,
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/ns-interface.expected.txt"),
        1,
    );
}

#[test]
fn ns_missing_hidden_bare_and_trailing_diagnose() {
    expect_differential(
        "ns_missing_hidden_bare_and_trailing_diagnose",
        include_str!("../../../corpus/check-enums-namespaces/ns-missing.ts"),
        &[
            HandFed {
                name: "a",
                kind: DeclKind::Const,
                annotation: Some("NS.Nope"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
            HandFed {
                name: "h",
                kind: DeclKind::Const,
                annotation: Some("NS.Hidden"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("0"),
            },
            HandFed {
                name: "n",
                kind: DeclKind::Const,
                annotation: Some("NS"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
            HandFed {
                name: "m",
                kind: DeclKind::Const,
                annotation: Some("Outer.Inner"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
            HandFed {
                name: "q",
                kind: DeclKind::Const,
                annotation: Some("NS.Point.X"),
                init: Some(InitKind::Number),
                members: None,
                init_text: Some("1"),
            },
        ],
        include_str!("../../../corpus/check-enums-namespaces/ns-missing.expected.txt"),
        0,
    );
}

#[test]
fn unresolved_qualification_head_skips_silently() {
    // tsc reports `TS2503: Cannot find namespace 'NS2'.` here (probed
    // 7.0.2); the solver folds it into the existing unresolved tracking
    // (the check_calls precedent: tracked once, never double-diagnosed),
    // so the report is empty on both sinks.
    let source = "const u: NS2.Foo = 1;\n";
    let specs = [HandFed {
        name: "u",
        kind: DeclKind::Const,
        annotation: Some("NS2.Foo"),
        init: Some(InitKind::Number),
        members: None,
        init_text: Some("1"),
    }];
    let parsed = parse_module(FILE, "fixture.ts", source);
    assert!(parsed.errors.is_empty());
    let binder = build_binder(&parsed);
    assert!(
        binder
            .unresolved()
            .iter()
            .any(|entry| entry.file == FILE && entry.name == "NS2"),
        "head is tracked as unresolved"
    );
    let decls = decls_from_handfed(&parsed, &binder, source, &specs);
    let enums = enums_from_facts(&parsed, &binder);
    let interfaces = interfaces_from_facts(&parsed, &binder);
    let namespaces = namespaces_from_facts(&parsed, &binder);
    let input = EnumInput {
        enums: &enums,
        interfaces: &interfaces,
        namespaces: &namespaces,
    };
    let mut db = QueryDb::new();
    let report = check_enums(FILE, &decls, &input, &binder, &mut db);
    assert!(report.diagnostics.is_empty());
    assert!(report.unsupported.is_empty());
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-enums-namespaces/ns-missing.ts");
    let specs = [HandFed {
        name: "a",
        kind: DeclKind::Const,
        annotation: Some("NS.Nope"),
        init: Some(InitKind::Number),
        members: None,
        init_text: Some("1"),
    }];
    let first = run_pipeline(source, &specs);
    let second = run_pipeline(source, &specs);
    assert_eq!(first, second);
}

#[test]
fn driver_anchors_every_name_and_links_shapes() {
    // Guards every seam: each driven name binds a real symbol with a real
    // scope and a non-degenerate span; each shape fact links the same
    // identity the declarators resolve; namespace body scopes contain their
    // member symbols; literal texts slice the adapter's own init spans.
    let source = include_str!("../../../corpus/check-enums-namespaces/ns-enum.ts");
    let parsed = parse_module(FILE, "fixture.ts", source);
    assert!(parsed.errors.is_empty());
    let binder = build_binder(&parsed);
    let enums = enums_from_facts(&parsed, &binder);
    let namespaces = namespaces_from_facts(&parsed, &binder);
    assert_eq!(namespaces.len(), 1);
    let ns = &namespaces[0];
    assert_eq!(ns.name, "NS");
    assert_ne!(ns.body_scope, u32::MAX);
    assert!(ns.exported_members.contains(&"Dir".to_owned()));
    assert!(ns.exported_members.contains(&"VAL".to_owned()));
    let dir_symbol = parsed
        .symbols
        .iter()
        .find(|symbol| symbol.name == "Dir")
        .expect("Dir symbol");
    assert_eq!(dir_symbol.scope, ns.body_scope);
    assert_eq!(enums.len(), 1);
    assert_eq!(enums[0].name, "Dir");
    assert!(enums[0].exported);
    assert!(!enums[0].declared && !enums[0].is_const);
    assert_eq!(enums[0].members.len(), 2);
    let specs = [HandFed {
        name: "bad",
        kind: DeclKind::Const,
        annotation: Some("NS.Dir"),
        init: Some(InitKind::Number),
        members: None,
        init_text: Some("9"),
    }];
    let decls = decls_from_handfed(&parsed, &binder, source, &specs);
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].decl.name, "bad");
    assert_eq!(decls[0].decl.span.file, FILE);
    assert!(decls[0].decl.span.lo < decls[0].decl.span.hi);
    assert!(decls[0].decl.symbol.is_some());
    assert_eq!(decls[0].init_text.as_deref(), Some("9"));
}
