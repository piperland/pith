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
//! else). Structural admission (P062) checks object-literal arguments
//! member-wise against LOCAL interface shapes through the shared P017
//! comparison: `named-structural-clean`/`wrong`/`excess`/`missing` match
//! their oracle families with zero unsupported, while
//! `named-structural-imported-declined` (no local shape — legacy decline),
//! `named-structural-methoded-declined` (methoded shape — complex-member
//! decline), `named-structural-nonliteral.ts` (identifier args
//! decline distinctly, call results keep the opaque decline), and
//! `named-alias-call-declined` (no alias tables — opaque decline) pin
//! their divergences explicitly. Object-literal members ride per-fixture
//! hand-fed tables ([`NamedArgShape`] — the adapter emits no call-argument
//! member facts); identifier names slice from fact spans (the P061 seam);
//! everything else keeps the zero-hand-feeding rule. Overload any-match,
//! union arities, and the gap spelling
//! all match (P044 converted the old `overloads-declined` divergence into
//! a `TS2554` match). Ranges, rest minima, and rest-element checks all
//! match (P037 converted the old `rest-param-declined` divergence into a
//! silent match). Ambient declarations (P063) check through the same paths:
//! single `declare function` sites (`ambient-clean`/`wrong-type`/`too-few`/
//! `too-many`) and ambient overload groups (`ambient-overload-clean`/
//! `wrong`) match their oracle families with zero unsupported, while
//! `ts2391-impl-less-group` (oracle `TS2391` on the declaration plus
//! `TS2769` on the call — solver one `PITH2769`, never a declaration
//! diagnostic), `overload-impl-excluded` (the implementation signature
//! never participates — solver one `PITH2345` like the oracle),
//! `ambient-overload-generic-declined` (generic exclusion against a clean
//! oracle), and `non-callable-ambient-declined` (oracle `TS2349`, solver
//! one unsupported with the no-signature reason) pin their divergences
//! explicitly. Contextual arrows (P064) bind unannotated params from
//! admitted function-typed params (inline or one alias level) and check
//! bodies through the existing delegation: `contextual-clean`/`wrong-body`
//! and `named-alias-clean` match their oracle families with zero
//! unsupported, while `rest-declined`, `destructured-declined`,
//! `free-standing-declined` (unannotated-callee gate, as before), and
//! `returns-dependent-declined` (generic `T` never admits) pin their
//! divergences explicitly. Arrow facts ride per-fixture hand-fed tables
//! ([`ArrowArgShape`] — the adapter emits no arrow facts); identifier
//! names never slice for arrows (explicit tables only).

use pith_frontend::{
    parse_module, CallArgFact as FrontendCallArg, CallArgKind as FrontendCallArgKind,
    FunctionBodyFact, ParsedFile, ReturnKind as FrontendReturnKind,
    SingleReturnFact as FrontendReturn,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_solver::{
    check_calls, check_calls_with_named_types, ArrowBody, ArrowInit, ArrowParam, CallArg, CallSite,
    FileReport, FunctionBody, FunctionDecl, FunctionParam, FunctionReturn, InitKind,
    InterfaceHeritage, InterfaceMember, InterfaceShape, JoinedReturns, NamedTypeScope, ObjectInit,
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
        member_ref: None,
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
                        // No default-kind facts here (the check-functions
                        // driver owns the P070 mapping): `None` keeps the
                        // historical optional decline.
                        default_kind: None,
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
                    // Non-generic call drivers never feed identifier names.
                    ident: None,
                    // Fact-only drivers never feed object members (see
                    // `calls_from_facts_named` for the hand-fed seam).
                    arg_object: None,
                    // Fact-only drivers never feed arrow expressions (see
                    // `calls_from_facts_contextual` for the hand-fed seam).
                    arg_arrow: None,
                })
                .collect(),
        })
        .collect()
}

/// Slices `source` at a fact span (`None` on skew — only possible with
/// recovery from parse errors; mirrors the check-const driver's seam).
fn slice_of(source: &str, span: Span) -> Option<&str> {
    let lo = usize::try_from(span.lo).ok()?;
    let hi = usize::try_from(span.hi).ok()?;
    source.get(lo..hi)
}

/// Whether sliced text is a bare identifier (mirrors the check-const
/// driver's check).
fn is_bare_identifier(text: &str) -> bool {
    !text.is_empty()
        && text
            .chars()
            .all(|character| character.is_alphanumeric() || character == '_' || character == '$')
}

/// Slices one call argument's bare-identifier name (the P061 seam): `Some`
/// only for `NonLiteral` arguments whose fact span slices to a bare
/// identifier — literals and every other shape feed `None` and keep their
/// historical paths.
fn call_arg_ident(source: &str, arg: &FrontendCallArg) -> Option<String> {
    if arg.kind != FrontendCallArgKind::NonLiteral {
        return None;
    }
    slice_of(source, arg.span)
        .filter(|text| is_bare_identifier(text))
        .map(str::to_owned)
}

/// One hand-fed object-literal argument shape (P062): the `call`-th call in
/// file order, its `arg`-th argument, and the member facts the adapter
/// cannot emit yet. Drivers feed one entry per object-literal argument in
/// the fixture; every other argument keeps `arg_object: None` (identifiers
/// slice their name through the P061 seam above, everything else stays
/// unshaped and keeps the opaque decline).
struct NamedArgShape<'a> {
    /// Index into [`ParsedFile::calls`] in file order.
    call: usize,
    /// Index into the call's arguments.
    arg: usize,
    /// Member facts in literal source order.
    members: &'a [(&'a str, ObjectMemberKind)],
}

/// The named-type call-site driver: adapter facts plus two disclosed seams —
/// sliced identifier names (P061) and hand-fed object-literal members
/// (P062, asserted fresh literals below). Arity, spans, and shapes still
/// come from facts; only the sliced names and member lists are hand-fed,
/// and both vanish when the adapter emits the facts.
fn calls_from_facts_named(
    parsed: &ParsedFile,
    source: &str,
    shapes: &[NamedArgShape<'_>],
) -> Vec<CallSite> {
    parsed
        .calls
        .iter()
        .enumerate()
        .map(|(call_index, call)| CallSite {
            callee: call.callee.clone(),
            callee_span: call.callee_span,
            span: call.span,
            args: call
                .args
                .iter()
                .enumerate()
                .map(|(arg_index, arg)| {
                    let arg_object = shapes
                        .iter()
                        .find(|shape| shape.call == call_index && shape.arg == arg_index)
                        .map(|shape| {
                            assert_eq!(
                                arg.kind,
                                FrontendCallArgKind::NonLiteral,
                                "shaped args are object literals"
                            );
                            assert!(arg.cast.is_none(), "shaped args carry no assertions");
                            ObjectInit {
                                members: shape
                                    .members
                                    .iter()
                                    .map(|(name, kind)| ObjectMemberInit {
                                        name: (*name).to_owned(),
                                        kind: *kind,
                                    })
                                    .collect(),
                                fresh: true,
                            }
                        });
                    CallArg {
                        kind: map_call_arg_kind(arg.kind),
                        span: arg.span,
                        cast: None,
                        ident: call_arg_ident(source, arg),
                        arg_object,
                        // Contextual drivers never feed arrow expressions
                        // here (see `calls_from_facts_contextual`).
                        arg_arrow: None,
                    }
                })
                .collect(),
        })
        .collect()
}

/// One hand-fed arrow argument shape (P064): the `call`-th call in file
/// order, its `arg`-th argument, and the arrow facts the adapter cannot
/// emit yet. Drivers feed one entry per arrow argument in the fixture;
/// every other argument keeps `arg_arrow: None` (literals check
/// primitively, identifiers slice their name through the P061 seam,
/// everything else stays unshaped). The kind stays
/// [`FrontendCallArgKind::NonLiteral`] either way (asserted below —
/// exactly like the frontend classifies arrows), casts never ride arrows,
/// and body/arrow spans approximate to the argument span (differentials
/// compare codes plus messages only). Both seams vanish when the adapter
/// emits the facts.
struct ArrowArgShape<'a> {
    /// Index into [`ParsedFile::calls`] in file order.
    call: usize,
    /// Index into the call's arguments.
    arg: usize,
    /// Arrow parameters in source order: names plus whether each is a
    /// `...rest` parameter (unannotated identifiers either way — annotated
    /// arrow parameters are unit-tested only, never fixture-fed).
    params: &'a [(&'a str, bool)],
    /// `true` for destructured parameter patterns (the solver declines).
    params_complex: bool,
    /// Literal kind of the expression body.
    body_kind: FrontendCallArgKind,
    /// Bare-identifier body name (`Some("x")` for `(x) => x`); `None` for
    /// literal bodies. Non-identifier non-literal bodies feed `None` and
    /// ride the existing per-position decline.
    body_ident: Option<&'a str>,
    /// `true` for block bodies (the solver declines).
    body_complex: bool,
}

/// The contextual call-site driver: adapter facts plus the hand-fed arrow
/// seam ([`ArrowArgShape`] — asserted `NonLiteral` with no cast, like the
/// P062 object seam). Arity and spans still come from facts; only the
/// parameter lists and body shapes are hand-fed, and both vanish when the
/// adapter emits arrow facts.
fn calls_from_facts_contextual(parsed: &ParsedFile, arrows: &[ArrowArgShape<'_>]) -> Vec<CallSite> {
    parsed
        .calls
        .iter()
        .enumerate()
        .map(|(call_index, call)| CallSite {
            callee: call.callee.clone(),
            callee_span: call.callee_span,
            span: call.span,
            args: call
                .args
                .iter()
                .enumerate()
                .map(|(arg_index, arg)| {
                    let arg_arrow = arrows
                        .iter()
                        .find(|shape| shape.call == call_index && shape.arg == arg_index)
                        .map(|shape| {
                            assert_eq!(
                                arg.kind,
                                FrontendCallArgKind::NonLiteral,
                                "arrow args classify NonLiteral"
                            );
                            assert!(arg.cast.is_none(), "arrow args carry no assertions");
                            ArrowInit {
                                params: shape
                                    .params
                                    .iter()
                                    .map(|(name, is_rest)| ArrowParam {
                                        name: (*name).to_owned(),
                                        annotated: false,
                                        annotation: None,
                                        is_rest: *is_rest,
                                    })
                                    .collect(),
                                params_complex: shape.params_complex,
                                body: ArrowBody {
                                    kind: map_call_arg_kind(shape.body_kind),
                                    span: arg.span,
                                    ident: shape.body_ident.map(str::to_owned),
                                },
                                body_complex: shape.body_complex,
                                span: arg.span,
                            }
                        });
                    CallArg {
                        kind: map_call_arg_kind(arg.kind),
                        span: arg.span,
                        cast: None,
                        // Contextual fixtures hold no bare-identifier
                        // arguments (arrows never slice); every other shape
                        // keeps the historical skip.
                        ident: None,
                        arg_object: None,
                        arg_arrow,
                    }
                })
                .collect(),
        })
        .collect()
}

/// Maps every [`ParsedFile::aliases`] fact onto a [`TypeAliasShape`]
/// (mechanical name + target copy, mirroring the check-const driver;
/// binding spans stay frontend-side — decline reasons anchor at use
/// sites).
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
/// Maps every [`ParsedFile::interfaces`] fact onto an [`InterfaceShape`]
/// (mechanical copy of the check-interfaces driver, with the binder
/// [`SymbolId`] resolved from the checking [`Binder`] — the linkage that
/// tells a local shape from an imported name).
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
    run_pipeline_named_shaped(source, &[])
}

/// Runs the named pipeline with hand-fed object-literal argument shapes
/// (P062): `shapes` feeds one member list per object-literal argument (see
/// [`NamedArgShape`]); interface shapes map from facts (see
/// [`shapes_from_facts`]).
fn run_pipeline_named_shaped(
    source: &str,
    arg_shapes: &[NamedArgShape<'_>],
) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts_named(&parsed, source, arg_shapes);
    let mut owned: Vec<String> = parsed
        .interfaces
        .iter()
        .map(|interface| interface.name.clone())
        .collect();
    owned.extend(parsed.aliases.iter().map(|alias| alias.name.clone()));
    let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
    let shapes = shapes_from_facts(&parsed, &binder);
    let aliases = aliases_from_facts(&parsed);
    let scope = NamedTypeScope {
        names: &refs,
        interfaces: &shapes,
        aliases: &aliases,
    };
    let report = check_calls_with_named_types(FILE, &decls, &calls, &binder, &scope);
    (parsed, report)
}

/// Runs the contextual pipeline with hand-fed arrow argument shapes
/// (P064): `arrows` feeds one [`ArrowArgShape`] per arrow argument (see the
/// struct docs); interface shapes and alias shapes map from facts (see
/// [`shapes_from_facts`] and [`aliases_from_facts`]).
fn run_pipeline_contextual(source: &str, arrows: &[ArrowArgShape<'_>]) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder);
    let calls = calls_from_facts_contextual(&parsed, arrows);
    let mut owned: Vec<String> = parsed
        .interfaces
        .iter()
        .map(|interface| interface.name.clone())
        .collect();
    owned.extend(parsed.aliases.iter().map(|alias| alias.name.clone()));
    let refs: Vec<&str> = owned.iter().map(String::as_str).collect();
    let shapes = shapes_from_facts(&parsed, &binder);
    let aliases = aliases_from_facts(&parsed);
    let scope = NamedTypeScope {
        names: &refs,
        interfaces: &shapes,
        aliases: &aliases,
    };
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

fixture_test!(
    ambient_clean_calls_are_silent,
    "ambient-clean.ts",
    "ambient-clean.expected.txt",
    0
);
fixture_test!(
    ambient_wrong_type_matches_ts2345,
    "ambient-wrong-type.ts",
    "ambient-wrong-type.expected.txt",
    0
);
fixture_test!(
    ambient_too_few_matches_ts2554,
    "ambient-too-few.ts",
    "ambient-too-few.expected.txt",
    0
);
fixture_test!(
    ambient_too_many_matches_ts2554,
    "ambient-too-many.ts",
    "ambient-too-many.expected.txt",
    0
);
fixture_test!(
    ambient_overload_clean_calls_are_silent,
    "ambient-overload-clean.ts",
    "ambient-overload-clean.expected.txt",
    0
);
fixture_test!(
    ambient_overload_wrong_all_matches_ts2769,
    "ambient-overload-wrong.ts",
    "ambient-overload-wrong.expected.txt",
    0
);
fixture_test!(
    overload_impl_excluded_matches_ts2345,
    "overload-impl-excluded.ts",
    "overload-impl-excluded.expected.txt",
    0
);

#[test]
fn ambient_overload_generic_declines_and_pins_clean_oracle() {
    // P063: the generic ambient signature rides the existing exclusion —
    // the first call stays silent through the remaining checkable signature
    // while the second records one unsupported note (the oracle instantiates
    // `T` and stays clean on both — pinned divergence, never a forced
    // `TS2769`).
    let source = include_str!("../../../corpus/check-calls/ambient-overload-generic-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/ambient-overload-generic-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on both calls"
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
fn ts2391_impl_less_group_resolves_calls_and_pins_ts2391() {
    // P063: calls over an implementation-less group still resolve by
    // any-match (one `PITH2769` on the wrong call) while the oracle's
    // `TS2391` on the declaration stays declined — the solver spells no
    // declaration diagnostics.
    let source = include_str!("../../../corpus/check-calls/ts2391-impl-less-group.ts");
    let expected = include_str!("../../../corpus/check-calls/ts2391-impl-less-group.expected.txt");
    let last_error = concat!(
        "No overload matches this call.\n",
        "  The last overload gave the following error.\n",
        "    Argument of type 'boolean' is not assignable to parameter of type 'string'."
    );
    assert_eq!(
        parse_baseline(expected),
        [
            (
                "TS2391".to_owned(),
                "Function implementation is missing or not immediately following the declaration."
                    .to_owned()
            ),
            ("TS2769".to_owned(), last_error.to_owned()),
        ],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline(source);
    assert_eq!(report.diagnostics.len(), 1);
    assert_eq!(report.diagnostics[0].code, "PITH2769");
    assert_eq!(report.diagnostics[0].message, last_error);
    assert!(
        report.unsupported.is_empty(),
        "unsupported: {:?}",
        report.unsupported
    );
}

#[test]
fn non_callable_ambient_declines_distinctly_and_pins_ts2349() {
    // P063: `declare const` binds the name with no function signature — tsc
    // spells `TS2349` (plus a lib-spelled continuation) while the solver
    // records one unsupported note with its own reason (never a forced
    // verdict, never the undeclared-name skew).
    let source = include_str!("../../../corpus/check-calls/non-callable-ambient-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/non-callable-ambient-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2349".to_owned(),
            "This expression is not callable.\n  Type 'Number' has no call signatures.".to_owned()
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
    assert_eq!(
        report.unsupported[0].reason,
        "call to 'nc': the name declares no function signature: outside the subset"
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

/// Asserts the named pipeline verdict differentially equals the recorded
/// baseline with hand-fed object-literal argument shapes (P062): same
/// `(code-family, message)` multiset (`TS`/`PITH` prefixes folded) and the
/// expected unsupported count, with sane anchored spans throughout.
fn expect_differential_named(
    name: &str,
    source: &str,
    expected: &str,
    unsupported: usize,
    arg_shapes: &[NamedArgShape<'_>],
) {
    let (_, report) = run_pipeline_named_shaped(source, arg_shapes);
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

#[test]
fn named_structural_clean_matches_oracle() {
    // P062: a matching object arg checks member-wise against the local
    // shape — silent on both sides.
    let source = include_str!("../../../corpus/check-calls/named-structural-clean.ts");
    let expected = include_str!("../../../corpus/check-calls/named-structural-clean.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the matching call"
    );
    expect_differential_named(
        "named_structural_clean_matches_oracle",
        source,
        expected,
        0,
        &[NamedArgShape {
            call: 0,
            arg: 0,
            members: &[
                ("x", ObjectMemberKind::Number),
                ("y", ObjectMemberKind::String),
            ],
        }],
    );
}

#[test]
fn named_structural_wrong_matches_ts2322() {
    // P062: one `TS2322` per wrong member, first-mismatch per call (probed
    // 7.0.2 `b`/`i`).
    let source = include_str!("../../../corpus/check-calls/named-structural-wrong.ts");
    let expected = include_str!("../../../corpus/check-calls/named-structural-wrong.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [
            (
                "TS2322".to_owned(),
                "Type 'number' is not assignable to type 'string'.".to_owned()
            ),
            (
                "TS2322".to_owned(),
                "Type 'string' is not assignable to type 'number'.".to_owned()
            ),
            (
                "TS2322".to_owned(),
                "Type 'string' is not assignable to type 'number'.".to_owned()
            ),
        ],
        "oracle baseline pins the per-member verdicts"
    );
    expect_differential_named(
        "named_structural_wrong_matches_ts2322",
        source,
        expected,
        0,
        &[
            NamedArgShape {
                call: 0,
                arg: 0,
                members: &[
                    ("x", ObjectMemberKind::String),
                    ("y", ObjectMemberKind::String),
                ],
            },
            NamedArgShape {
                call: 1,
                arg: 0,
                members: &[
                    ("x", ObjectMemberKind::String),
                    ("y", ObjectMemberKind::Number),
                ],
            },
        ],
    );
}

#[test]
fn named_structural_excess_matches_ts2353() {
    // P062: first-excess `TS2353` spelling the interface name (probed 7.0.2
    // `c`).
    let source = include_str!("../../../corpus/check-calls/named-structural-excess.ts");
    let expected = include_str!("../../../corpus/check-calls/named-structural-excess.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2353".to_owned(),
            "Object literal may only specify known properties, and 'extra' does not exist in \
            type 'Point'."
                .to_owned()
        )],
        "oracle baseline pins the excess verdict"
    );
    expect_differential_named(
        "named_structural_excess_matches_ts2353",
        source,
        expected,
        0,
        &[NamedArgShape {
            call: 0,
            arg: 0,
            members: &[
                ("x", ObjectMemberKind::Number),
                ("extra", ObjectMemberKind::Number),
            ],
        }],
    );
}

#[test]
fn named_structural_missing_matches_ts2741_and_ts2739() {
    // P062: one missing member spells `TS2741`, several collapse into one
    // `TS2739` (probed 7.0.2 `d`/`e`).
    let source = include_str!("../../../corpus/check-calls/named-structural-missing.ts");
    let expected =
        include_str!("../../../corpus/check-calls/named-structural-missing.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [
            (
                "TS2739".to_owned(),
                "Type '{ a: number; }' is missing the following properties from type 'Big': \
                b, c"
                    .to_owned()
            ),
            (
                "TS2741".to_owned(),
                "Property 'y' is missing in type '{ x: number; }' but required in type \
                'Point'."
                    .to_owned()
            ),
        ],
        "oracle baseline pins the missing verdicts (parser sorts pairs)"
    );
    expect_differential_named(
        "named_structural_missing_matches_ts2741_and_ts2739",
        source,
        expected,
        0,
        &[
            NamedArgShape {
                call: 0,
                arg: 0,
                members: &[("x", ObjectMemberKind::Number)],
            },
            NamedArgShape {
                call: 1,
                arg: 0,
                members: &[("a", ObjectMemberKind::Number)],
            },
        ],
    );
}

#[test]
fn named_structural_imported_declines_and_pins_ts2322() {
    // P062: the imported name claims no local shape, so the call keeps the
    // legacy decline while tsc checks it (probed 7.0.2 `s-imp`) — a pinned
    // oracle-error divergence, never a forced verdict.
    let source = include_str!("../../../corpus/check-calls/named-structural-imported-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/named-structural-imported-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
        )],
        "oracle baseline pins the divergence"
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
        "call to 'show': parameter type 'Point' for 'p' is outside the subset"
    );
}

#[test]
fn named_structural_methoded_declines_and_pins_clean_oracle() {
    // P062: method members carry no value-type facts, so the shape declines
    // inside the shared comparison while tsc is clean (probed 7.0.2
    // `g-methoded`) — a pinned oracle-clean divergence.
    let source = include_str!("../../../corpus/check-calls/named-structural-methoded-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/named-structural-methoded-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the complete methoded call"
    );
    let (_, report) = run_pipeline_named_shaped(
        source,
        &[NamedArgShape {
            call: 0,
            arg: 0,
            members: &[
                ("x", ObjectMemberKind::Number),
                ("run", ObjectMemberKind::NonLiteral),
            ],
        }],
    );
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("member 'run'"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn named_structural_nonliteral_declines_and_pins_clean_oracle() {
    // P062: the identifier arg declines with its own reason (no value-type
    // facts) while the call-result arg keeps the opaque decline; tsc is
    // clean on both (probed 7.0.2 `f-nonliteral`) — pinned divergences,
    // never silent.
    let source = include_str!("../../../corpus/check-calls/named-structural-nonliteral.ts");
    let expected =
        include_str!("../../../corpus/check-calls/named-structural-nonliteral.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on both non-literal calls"
    );
    let (parsed, report) = run_pipeline_named(source);
    let shows = parsed
        .calls
        .iter()
        .filter(|call| call.callee == "show")
        .count();
    assert_eq!(shows, 2, "both show calls emit facts");
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 2);
    assert!(
        report.unsupported[0].reason.contains("identifier argument"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(
        !report.unsupported[0].reason.contains("opaque"),
        "reason: {}",
        report.unsupported[0].reason
    );
    assert!(
        report.unsupported[1].reason.contains("opaque named type"),
        "reason: {}",
        report.unsupported[1].reason
    );
}

#[test]
fn named_alias_call_declines_and_pins_ts2322() {
    // P062 follow-up pin: call sites thread no alias tables, so alias-named
    // params keep the opaque decline while tsc checks them (probed 7.0.2
    // `o-alias-iface`) — a pinned oracle-error divergence.
    let source = include_str!("../../../corpus/check-calls/named-alias-call-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/named-alias-call-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline_named(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("opaque named type"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

/// Asserts the contextual pipeline verdict differentially equals the
/// recorded baseline with hand-fed arrow argument shapes (P064): same
/// `(code-family, message)` multiset (`TS`/`PITH` prefixes folded) and the
/// expected unsupported count, with sane anchored spans throughout.
fn expect_differential_contextual(
    name: &str,
    source: &str,
    expected: &str,
    unsupported: usize,
    arrows: &[ArrowArgShape<'_>],
) {
    let (_, report) = run_pipeline_contextual(source, arrows);
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

#[test]
fn contextual_clean_matches_oracle() {
    // P064: unannotated arrow params bind from the expected signature —
    // literal bodies, identifier bodies resolving through the bound params,
    // and multi-param arrows all stay silent like the oracle.
    let source = include_str!("../../../corpus/check-calls/contextual-clean.ts");
    let expected = include_str!("../../../corpus/check-calls/contextual-clean.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on all three calls"
    );
    expect_differential_contextual(
        "contextual_clean_matches_oracle",
        source,
        expected,
        0,
        &[
            ArrowArgShape {
                call: 0,
                arg: 0,
                params: &[("x", false)],
                params_complex: false,
                body_kind: FrontendCallArgKind::Number,
                body_ident: None,
                body_complex: false,
            },
            ArrowArgShape {
                call: 1,
                arg: 0,
                params: &[("x", false)],
                params_complex: false,
                body_kind: FrontendCallArgKind::NonLiteral,
                body_ident: Some("x"),
                body_complex: false,
            },
            ArrowArgShape {
                call: 2,
                arg: 0,
                params: &[("x", false), ("y", false)],
                params_complex: false,
                body_kind: FrontendCallArgKind::Number,
                body_ident: None,
                body_complex: false,
            },
        ],
    );
}

#[test]
fn contextual_wrong_body_matches_ts2322() {
    // P064: wrong arrow bodies diagnose once per call at the body span
    // (probed 7.0.2: `TS2322` naming the widened body kind).
    let source = include_str!("../../../corpus/check-calls/contextual-wrong-body.ts");
    let expected = include_str!("../../../corpus/check-calls/contextual-wrong-body.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [
            (
                "TS2322".to_owned(),
                "Type 'string' is not assignable to type 'number'.".to_owned()
            ),
            (
                "TS2322".to_owned(),
                "Type 'string' is not assignable to type 'number'.".to_owned()
            ),
        ],
        "oracle baseline pins the per-call verdicts"
    );
    expect_differential_contextual(
        "contextual_wrong_body_matches_ts2322",
        source,
        expected,
        0,
        &[
            ArrowArgShape {
                call: 0,
                arg: 0,
                params: &[("x", false)],
                params_complex: false,
                body_kind: FrontendCallArgKind::String,
                body_ident: None,
                body_complex: false,
            },
            ArrowArgShape {
                call: 1,
                arg: 0,
                params: &[("x", false), ("y", false)],
                params_complex: false,
                body_kind: FrontendCallArgKind::NonLiteral,
                body_ident: Some("y"),
                body_complex: false,
            },
        ],
    );
}

#[test]
fn named_alias_function_type_matches_oracle() {
    // P064: a bare name claimed by exactly one non-generic alias to an
    // admitted function type binds contextually (probed 7.0.2 `i` clean).
    let source = include_str!("../../../corpus/check-calls/named-alias-clean.ts");
    let expected = include_str!("../../../corpus/check-calls/named-alias-clean.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the alias-typed call"
    );
    expect_differential_contextual(
        "named_alias_function_type_matches_oracle",
        source,
        expected,
        0,
        &[ArrowArgShape {
            call: 0,
            arg: 0,
            params: &[("x", false)],
            params_complex: false,
            body_kind: FrontendCallArgKind::Number,
            body_ident: None,
            body_complex: false,
        }],
    );
}

#[test]
fn rest_arrow_declines_and_pins_clean_oracle() {
    // P064: rest arrow params decline distinctly while tsc checks them
    // (probed 7.0.2 `c` clean) — a pinned oracle-clean divergence.
    let source = include_str!("../../../corpus/check-calls/rest-declined.ts");
    let expected = include_str!("../../../corpus/check-calls/rest-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the rest arrow"
    );
    let (_, report) = run_pipeline_contextual(
        source,
        &[ArrowArgShape {
            call: 0,
            arg: 0,
            params: &[("args", true)],
            params_complex: false,
            body_kind: FrontendCallArgKind::Number,
            body_ident: None,
            body_complex: false,
        }],
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
            .contains("rest arrow parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn destructured_arrow_declines_and_pins_ts2339() {
    // P064: destructured arrow params decline distinctly while tsc spells
    // `TS2339` (probed 7.0.2 `d`) — a pinned oracle-error divergence.
    let source = include_str!("../../../corpus/check-calls/destructured-declined.ts");
    let expected = include_str!("../../../corpus/check-calls/destructured-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2339".to_owned(),
            "Property 'x' does not exist on type 'Number'.".to_owned()
        )],
        "oracle baseline pins the divergence"
    );
    let (_, report) = run_pipeline_contextual(
        source,
        &[ArrowArgShape {
            call: 0,
            arg: 0,
            params: &[],
            params_complex: true,
            body_kind: FrontendCallArgKind::Number,
            body_ident: None,
            body_complex: false,
        }],
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
            .contains("non-identifier arrow parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn free_standing_arrow_declines_as_before() {
    // P064: an arrow against an unannotated callee parameter keeps the
    // unannotated-parameter gate (the oracle spells two `TS7006`s — probed
    // 7.0.2 `w` — while the solver records the same note as before).
    let source = include_str!("../../../corpus/check-calls/free-standing-declined.ts");
    let expected = include_str!("../../../corpus/check-calls/free-standing-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected).len(),
        2,
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
            .contains("unannotated parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn returns_dependent_inference_stays_declined() {
    // P064: generic `T`-typed signatures never admit (the parameter kind
    // would come from the arrow's return), so the call declines as before
    // while tsc infers silently (probed 7.0.2 `f`/`r` clean).
    let source = include_str!("../../../corpus/check-calls/returns-dependent-declined.ts");
    let expected =
        include_str!("../../../corpus/check-calls/returns-dependent-declined.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on the generic call"
    );
    let (_, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
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
