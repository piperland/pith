//! Fact-anchored, shape-hand-fed solver end-to-end (PITH-P034): lib types.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] (real
//! scopes + symbols) -> [`decls_from_handfed`] + [`functions_from_handfed`]
//! -> [`check_file`]/[`check_functions`] -> [`FileReport`], then a
//! differential against the recorded tsc `.expected.txt` baselines.
//!
//! Division of labor: names, scopes, and spans come from adapter facts (each
//! hand-fed entry must name a real bound symbol); only SHAPES are hand-fed
//! (annotation text, array element facts, async flags, awaited return
//! kinds). Rationale: the adapter emits no array-member facts, no async
//! flag, classifies `await` (and every `[ ... ]` literal) as non-literal —
//! the same hand-fed seam as M1's `compute` closures and the solver's
//! documented P034 BLOCKER — so shapes ride per-fixture tables until the
//! adapter emits them. Awaited return kinds ride the same slot as plain
//! literal kinds (tsc's `await` transparency, probed 7.0.2): the seam
//! carries the awaited literal kind, disclosed here. Spans resolve
//! scope-sensitively through the binder, exactly like the check-object
//! driver.
//!
//! Differential rule: same as check-object — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322` <-> `PITH*`) plus the unsupported count for
//! declined fixtures.

use pith_frontend::parse_module;
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_file, check_functions, ArrayInit, ArrayMemberKind, ConstDecl, DeclKind, FileReport,
    FunctionBody, FunctionDecl, FunctionReturn, InitKind,
};
use pith_symbols::{Binder, ScopeInput, SymbolInput, UnresolvedInput};

const FILE: FileId = FileId(0);

/// Builds a fresh binder from one parsed file's scope/symbol/unresolved facts.
fn build_binder(parsed: &pith_frontend::ParsedFile) -> Binder {
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

/// Resolves one hand-fed name to its binder identity plus declaration span.
///
/// Names must be unique per fixture file so the lookup is unambiguous.
fn resolve_name(
    parsed: &pith_frontend::ParsedFile,
    binder: &Binder,
    name: &str,
) -> (u32, Option<SymbolId>, Span) {
    let symbol = parsed
        .symbols
        .iter()
        .find(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("hand-fed name '{name}' binds nothing"));
    let id: Option<SymbolId> = binder.resolve(parsed.file, symbol.scope, &symbol.name);
    let span: Span = id
        .and_then(|id| binder.store().get(id))
        .map_or(symbol.span, |found| found.span);
    (symbol.scope, id, span)
}

/// One hand-fed const shape: everything the adapter cannot emit yet.
///
/// `members: None` means "no array initializer"; `Some(&[])` means an empty
/// `[ ]` literal.
struct HandFed<'a> {
    name: &'a str,
    kind: DeclKind,
    annotation: Option<&'a str>,
    init: Option<InitKind>,
    members: Option<&'a [ArrayMemberKind]>,
}

/// One hand-fed function shape: async flag plus the return position.
///
/// `kind` is the returned (or awaited) literal kind; `members` carries
/// `[ ... ]` returns element-wise. `Some(NonLiteral)` kinds decline through
/// the existing position gate, exactly like other non-literal returns.
struct HandFedFn<'a> {
    name: &'a str,
    is_async: bool,
    return_annotation: &'a str,
    kind: Option<InitKind>,
    members: Option<&'a [ArrayMemberKind]>,
}

/// The shape-hand-fed const driver: spans/scopes/identities from adapter
/// facts, shapes from the per-fixture [`HandFed`] table.
fn decls_from_handfed(
    parsed: &pith_frontend::ParsedFile,
    binder: &Binder,
    specs: &[HandFed<'_>],
) -> Vec<ConstDecl> {
    specs
        .iter()
        .map(|spec| {
            let (scope, symbol, span) = resolve_name(parsed, binder, spec.name);
            ConstDecl {
                name: spec.name.to_owned(),
                span,
                scope,
                symbol,
                kind: spec.kind,
                annotation: spec.annotation.map(str::to_owned),
                init: spec.init,
                init_object: None,
                init_array: spec.members.map(|members| ArrayInit {
                    members: members.to_vec(),
                }),
                cast: None,
            }
        })
        .collect()
}

/// The shape-hand-fed function driver: single-return bodies only (every
/// lib fixture returns straight-line), async flags and return shapes from
/// the per-fixture [`HandFedFn`] table.
fn functions_from_handfed(
    parsed: &pith_frontend::ParsedFile,
    binder: &Binder,
    specs: &[HandFedFn<'_>],
) -> Vec<FunctionDecl> {
    specs
        .iter()
        .map(|spec| {
            let (scope, symbol, span) = resolve_name(parsed, binder, spec.name);
            FunctionDecl {
                name: spec.name.to_owned(),
                span,
                scope,
                symbol,
                params: Vec::new(),
                params_complex: false,
                is_async: spec.is_async,
                return_annotation: Some(spec.return_annotation.to_owned()),
                body: FunctionBody::SingleReturn(FunctionReturn {
                    kind: spec.kind,
                    init_object: None,
                    init_array: spec.members.map(|members| ArrayInit {
                        members: members.to_vec(),
                    }),
                    cast: None,
                }),
            }
        })
        .collect()
}

/// Runs the const pipeline on one fixture source with its hand-fed table.
fn run_consts(source: &str, specs: &[HandFed<'_>]) -> FileReport {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = decls_from_handfed(&parsed, &binder, specs);
    let mut db = QueryDb::new();
    check_file(FILE, &decls, &binder, &mut db)
}

/// Runs the function pipeline on one fixture source with its hand-fed table.
fn run_functions(source: &str, specs: &[HandFedFn<'_>]) -> FileReport {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_handfed(&parsed, &binder, specs);
    let mut db = QueryDb::new();
    check_functions(FILE, &decls, &binder, &mut db)
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

/// Asserts one pipeline verdict differentially equals the recorded baseline:
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

use ArrayMemberKind::{Boolean, Null, Number, String as ArrayString};

#[test]
fn array_correct_is_silent() {
    let report = run_consts(
        include_str!("../../../corpus/check-lib/array-correct.ts"),
        &[
            HandFed {
                name: "nums",
                kind: DeclKind::Const,
                annotation: Some("Array<number>"),
                init: None,
                members: Some(&[Number, Number, Number]),
            },
            HandFed {
                name: "names",
                kind: DeclKind::Const,
                annotation: Some("Array<string>"),
                init: None,
                members: Some(&[ArrayString, ArrayString]),
            },
            HandFed {
                name: "flags",
                kind: DeclKind::Const,
                annotation: Some("Array<boolean>"),
                init: None,
                members: Some(&[Boolean, Boolean]),
            },
            HandFed {
                name: "empty",
                kind: DeclKind::Const,
                annotation: Some("Array<number>"),
                init: None,
                members: Some(&[]),
            },
            HandFed {
                name: "nulls",
                kind: DeclKind::Const,
                annotation: Some("Array<null>"),
                init: None,
                members: Some(&[Null]),
            },
            HandFed {
                name: "mixed",
                kind: DeclKind::Const,
                annotation: Some("Array<any>"),
                init: None,
                members: Some(&[Number, ArrayString]),
            },
        ],
    );
    expect_differential(
        "array_correct_is_silent",
        &report,
        include_str!("../../../corpus/check-lib/array-correct.expected.txt"),
        0,
    );
}

#[test]
fn array_wrong_member_matches_ts2322() {
    let report = run_consts(
        include_str!("../../../corpus/check-lib/array-wrong-member.ts"),
        &[
            HandFed {
                name: "nums",
                kind: DeclKind::Const,
                annotation: Some("Array<number>"),
                init: None,
                members: Some(&[Number, ArrayString]),
            },
            HandFed {
                name: "flags",
                kind: DeclKind::Const,
                annotation: Some("Array<number>"),
                init: None,
                members: Some(&[Boolean]),
            },
            HandFed {
                name: "multi",
                kind: DeclKind::Const,
                annotation: Some("Array<number>"),
                init: None,
                members: Some(&[Number, ArrayString, Boolean]),
            },
        ],
    );
    expect_differential(
        "array_wrong_member_matches_ts2322",
        &report,
        include_str!("../../../corpus/check-lib/array-wrong-member.expected.txt"),
        0,
    );
}

#[test]
fn array_suffix_spelling_matches_oracle() {
    let report = run_consts(
        include_str!("../../../corpus/check-lib/array-suffix.ts"),
        &[
            HandFed {
                name: "ok",
                kind: DeclKind::Const,
                annotation: Some("number[]"),
                init: None,
                members: Some(&[Number, Number]),
            },
            HandFed {
                name: "bad",
                kind: DeclKind::Const,
                annotation: Some("string[]"),
                init: None,
                members: Some(&[Number]),
            },
            HandFed {
                name: "cross",
                kind: DeclKind::Const,
                annotation: Some("number"),
                init: None,
                members: Some(&[Number, Number]),
            },
        ],
    );
    expect_differential(
        "array_suffix_spelling_matches_oracle",
        &report,
        include_str!("../../../corpus/check-lib/array-suffix.expected.txt"),
        0,
    );
}

#[test]
fn promise_correct_is_silent() {
    let report = run_functions(
        include_str!("../../../corpus/check-lib/promise-correct.ts"),
        &[
            HandFedFn {
                name: "getCount",
                is_async: true,
                return_annotation: "Promise<number>",
                kind: Some(InitKind::Number),
                members: None,
            },
            HandFedFn {
                name: "getName",
                is_async: true,
                return_annotation: "Promise<string>",
                kind: Some(InitKind::String),
                members: None,
            },
            HandFedFn {
                name: "getIds",
                is_async: true,
                return_annotation: "Promise<Array<number>>",
                kind: None,
                members: Some(&[Number, Number]),
            },
            HandFedFn {
                name: "getAwaited",
                is_async: true,
                return_annotation: "Promise<number>",
                kind: Some(InitKind::Number),
                members: None,
            },
        ],
    );
    expect_differential(
        "promise_correct_is_silent",
        &report,
        include_str!("../../../corpus/check-lib/promise-correct.expected.txt"),
        0,
    );
}

#[test]
fn promise_wrong_matches_ts2322() {
    let report = run_functions(
        include_str!("../../../corpus/check-lib/promise-wrong.ts"),
        &[
            HandFedFn {
                name: "getCount",
                is_async: true,
                return_annotation: "Promise<number>",
                kind: Some(InitKind::String),
                members: None,
            },
            HandFedFn {
                name: "getName",
                is_async: true,
                return_annotation: "Promise<string>",
                kind: Some(InitKind::Number),
                members: None,
            },
            HandFedFn {
                name: "getIds",
                is_async: true,
                return_annotation: "Promise<Array<number>>",
                kind: None,
                members: Some(&[ArrayString]),
            },
            HandFedFn {
                name: "getBadAwaited",
                is_async: true,
                return_annotation: "Promise<number>",
                kind: Some(InitKind::String),
                members: None,
            },
        ],
    );
    expect_differential(
        "promise_wrong_matches_ts2322",
        &report,
        include_str!("../../../corpus/check-lib/promise-wrong.expected.txt"),
        0,
    );
}

#[test]
fn tuple_declined_with_reason() {
    let report = run_consts(
        include_str!("../../../corpus/check-lib/tuple-declined.ts"),
        &[HandFed {
            name: "pair",
            kind: DeclKind::Const,
            annotation: Some("[number, string]"),
            init: None,
            members: Some(&[Number, ArrayString]),
        }],
    );
    expect_differential(
        "tuple_declined_with_reason",
        &report,
        include_str!("../../../corpus/check-lib/tuple-declined.expected.txt"),
        1,
    );
}

#[test]
fn record_declined_with_reason() {
    let report = run_consts(
        include_str!("../../../corpus/check-lib/record-declined.ts"),
        &[HandFed {
            name: "scores",
            kind: DeclKind::Const,
            annotation: Some("Record<string, number>"),
            init: Some(InitKind::NonLiteral),
            members: None,
        }],
    );
    expect_differential(
        "record_declined_with_reason",
        &report,
        include_str!("../../../corpus/check-lib/record-declined.expected.txt"),
        1,
    );
}

#[test]
fn iterable_and_map_declined_with_reasons() {
    let report = run_consts(
        include_str!("../../../corpus/check-lib/iterable-map-declined.ts"),
        &[
            HandFed {
                name: "seq",
                kind: DeclKind::Const,
                annotation: Some("Iterable<number>"),
                init: None,
                members: Some(&[Number, Number]),
            },
            HandFed {
                name: "lookup",
                kind: DeclKind::Const,
                annotation: Some("Map<string, number>"),
                init: Some(InitKind::NonLiteral),
                members: None,
            },
        ],
    );
    expect_differential(
        "iterable_and_map_declined_with_reasons",
        &report,
        include_str!("../../../corpus/check-lib/iterable-map-declined.expected.txt"),
        2,
    );
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-lib/array-wrong-member.ts");
    let specs = [
        HandFed {
            name: "nums",
            kind: DeclKind::Const,
            annotation: Some("Array<number>"),
            init: None,
            members: Some(&[Number, ArrayString]),
        },
        HandFed {
            name: "flags",
            kind: DeclKind::Const,
            annotation: Some("Array<number>"),
            init: None,
            members: Some(&[Boolean]),
        },
        HandFed {
            name: "multi",
            kind: DeclKind::Const,
            annotation: Some("Array<number>"),
            init: None,
            members: Some(&[Number, ArrayString, Boolean]),
        },
    ];
    let first = run_consts(source, &specs);
    let second = run_consts(source, &specs);
    assert_eq!(first, second);
}

#[test]
fn driver_anchors_every_hand_fed_name_in_facts() {
    // Guards the hand-fed seam: every driven const and function name binds
    // a real symbol with a real scope and a non-degenerate span.
    let parsed = parse_module(
        FILE,
        "o.ts",
        "const p: Array<number> = [1];\nasync function f(): Promise<number> { return 1; }\n",
    );
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    let binder = build_binder(&parsed);
    let consts = decls_from_handfed(
        &parsed,
        &binder,
        &[HandFed {
            name: "p",
            kind: DeclKind::Const,
            annotation: Some("Array<number>"),
            init: None,
            members: Some(&[Number]),
        }],
    );
    assert_eq!(consts.len(), 1);
    assert_eq!(consts[0].name, "p");
    assert!(consts[0].symbol.is_some());
    let functions = functions_from_handfed(
        &parsed,
        &binder,
        &[HandFedFn {
            name: "f",
            is_async: true,
            return_annotation: "Promise<number>",
            kind: Some(InitKind::Number),
            members: None,
        }],
    );
    assert_eq!(functions.len(), 1);
    assert_eq!(functions[0].name, "f");
    assert!(functions[0].symbol.is_some());
}
