//! Fact-fed solver end-to-end (PITH-P013): function declarations.
//!
//! Pipeline per fixture: `parse_module` -> [`Binder::build_file`] ->
//! [`functions_from_facts`] (the driver: [`FunctionFact`](pith_frontend::FunctionFact)
//! to [`FunctionDecl`], zero hand-feeding) -> [`check_functions`] ->
//! [`FileReport`], then a differential against the recorded tsc
//! `.expected.txt` baselines.
//!
//! Division of labor: names, scopes, spans, parameter annotated-ness,
//! return annotations, and body shapes (including return-object member
//! facts) all come from adapter facts. Driver-side mapping is the
//! literal-kind enum translation (frontend [`ReturnKind`](pith_frontend::ReturnKind)
//! to solver [`InitKind`]/[`ObjectMemberKind`]), mechanical and exhaustive
//! like check-const's `map_init`, plus the P048 seam (bare-identifier
//! initializer names sliced from init fact spans — the adapter emits no
//! identifier-init facts). Returned object literals are always fresh
//! (only direct syntactic literals carry member facts), mirroring the
//! check-object seam's `fresh: true`.
//!
//! Differential rule: same as check-const — oracle lines are
//! `file:TSNNNN: message`, compared as sorted `(numeric-code, message)`
//! multisets (`TS2322` <-> `PITH2322`) plus the unsupported count.
//! Straight-line joins check per return (P023): `branching` (oracle `TS2322`
//! in the `else` branch) and the two-return/guard fixtures match their
//! baselines with zero unsupported notes, while `multi-return` (oracle
//! clean) is silent with zero notes. Straight bodies check per position
//! (P031): `straight-clean` (incl. unannotated-skip and nested-`function`
//! shapes) is silent with zero notes; `straight-inner-wrong` (incl. the
//! multi-declarator shape), `straight-tail-wrong`, `straight-object-inner`,
//! and `straight-nested-block` match their oracle `TS2322`s;
//! `straight-both-wrong` matches twice; `straight-unannotated-cast`
//! matches the oracle `TS2352`; `straight-identifier-init` matches its
//! oracle `TS2322` through single-level propagation (P048: the parameter's
//! declared type checks like a literal — first divergence-to-match flip).
//! One more fixture diverges by design (the oracle errors where the subset
//! declines): `straight-let-init-declined` (oracle `TS2322` on a
//! `let`-initialized inner declarator — `let` bindings never propagate,
//! pinned explicitly like `unannotated-param` below).
//! Try/catch bodies check per arm plus the optional tail (P039):
//! `try-clean` (incl. the clean tail) and `try-binding-unused` (plain
//! `catch (e)`, `e` unused) are silent with zero notes; `try-try-wrong`,
//! `try-catch-wrong`, and `try-tail-wrong` match their oracle `TS2322`s;
//! `try-both-wrong` matches twice. Three more fixtures diverge by design:
//! `try-finally-declined` and `try-throw-declined` (the oracle is clean
//! where the subset declines — each pins the clean baseline plus one
//! unsupported note) and `try-binding-used` (the oracle errors `TS2322`
//! on `unknown` where the subset rides the non-literal arm gate — silent
//! plus one unsupported note).
//! Switch bodies check per case plus the optional default (P040):
//! `switch-clean` is silent with zero notes; `switch-case-wrong` and
//! `switch-default-wrong` match their oracle `TS2322`s; `switch-two-wrong`
//! matches twice. Two more fixtures diverge by design (the oracle is clean
//! where the subset declines — each pins the clean baseline plus one
//! unsupported note): `switch-fallthrough-declined` and
//! `switch-complex-case-declined`.
//! Counted-`for` bodies check per position plus the optional tail (P041):
//! `for-clean` is silent with zero notes; `for-body-wrong` and
//! `for-zero-trip` match their oracle `TS2322`s (trip counts are not
//! modeled — the zero-trip body still reports). Three more fixtures diverge
//! by design: `for-nonliteral-bound-declined` (the oracle errors `TS2322`
//! where the subset rides the bound gate — silent plus one unsupported
//! note) and `for-while-declined` plus `for-complex-body-declined` (the
//! oracle is clean where the subset declines — each pins the clean baseline
//! plus one unsupported note).
//! Throw bodies check their non-throw positions while throws emit no
//! verdict (P043): `throw-guard-clean` (guard throw plus tail),
//! `throw-straight-clean` (mid-sequence throw), and `throw-only` are silent
//! with zero notes; `throw-guard-tail-wrong`, `throw-straight-inner-wrong`,
//! `throw-straight-tail-wrong`, and `throw-terminal-inner-wrong` (terminal
//! throw, no tail return) match their oracle `TS2322`s. One more fixture
//! diverges by design: `throw-complex-declined` (the oracle is clean where
//! the subset declines — pins the clean baseline plus one unsupported
//! note).
//! Void-effect bodies admit silently with zero positions while malformed
//! effect shapes decline distinctly (P049): `void-effect-clean` (lone
//! `console.warn` under `: void`) and `void-effect-guard-clean` (guard arm
//! plus bare tail) are silent with zero notes; `void-effect-guard-wrong`
//! matches its oracle `TS2322` on the tail (the arm emits nothing). Three
//! more fixtures diverge by design (the oracle is clean where the subset
//! declines — each pins the clean baseline plus one unsupported note with
//! its distinct reason): `void-effect-guard-two-calls`,
//! `void-effect-guard-nonallowlist`, and
//! `void-effect-guard-valued-return`.
//! Sequential guard-return chains check per guard plus the tail (P050):
//! `guard-chain-clean` is silent with zero notes; `guard-chain-wrong-guard`
//! and `guard-chain-wrong-tail` match their oracle `TS2322`s (positions
//! check independently — a wrong guard and a wrong tail each report once).
//! Two more fixtures diverge by design: `guard-chain-missing-tail` (the
//! oracle errors `TS2366` where the subset rides the missing-tail gate —
//! silent plus one unsupported note) and
//! `guard-chain-interleaved-declined` (the oracle is clean where the subset
//! declines on the mid-run `const` — pins the clean baseline plus one
//! unsupported note with its distinct reason). Guard-effect ident tails
//! compose with P048 (the V049 gap): `void-effect-guard-ident-tail`
//! matches its oracle `TS2322` (the bare-identifier tail resolves one level
//! to the string parameter, then checks like a literal).
//! Else-if chain bodies check per branch in source order (P045):
//! `elseif-clean` is silent with zero notes; `elseif-branch-wrong` matches
//! its oracle `TS2322`; `elseif-two-wrong` matches twice. Three more
//! fixtures diverge by design: `elseif-missing-else` (the oracle errors
//! `TS2366` where the subset rides the missing-else gate — silent plus one
//! unsupported note) and `elseif-nested-declined` plus
//! `elseif-complex-branch-declined` (the oracle is clean where the subset
//! declines — each pins the clean baseline plus one unsupported note with
//! its distinct reason).
//! Named (interface/alias) params admit as opaque (P046):
//! `named-param-clean` (interface + alias + primitive params) and
//! `named-param-unused` (untouched named param alongside checked positions)
//! are silent with zero notes; `named-param-body-wrong` matches its oracle
//! `TS2322`. No value-type facts about params flow anywhere: `return p`
//! rides the existing non-literal position gate, while `const y: T = p`
//! resolves one level through the identifier gate (P048) — primitively
//! annotated params check like their annotation, anything else declines
//! per-position (unit-pinned in `pith-solver`).
//! One fixture still diverges by design
//! (the oracle errors where the subset declines): `unannotated-param`
//! (oracle `TS7006`). That pins the divergence explicitly — oracle error
//! present, solver silent with one unsupported note — instead of forcing a
//! false match.
//! Ternary `c ? A : B` returns check per arm through two synthetic positions
//! (P051): `ternary-return-clean` is silent with zero notes;
//! `ternary-return-wrong-then` and `ternary-return-wrong-else` match their
//! oracle `TS2322`s (one arm each, at arm spans) while
//! `ternary-return-both-wrong` matches twice. Identifier arms resolve one
//! level (`ternary-return-ident`: the parameter arm diagnoses while the
//! clean declaration stays silent); `any` arms emit nothing while the
//! sibling still checks (`ternary-return-any-arm`), `unknown` arms check as
//! `unknown` (`ternary-return-unknown-arm`), and `never` arms vanish while
//! the sibling checks (`ternary-return-never-arm`). Two more fixtures
//! diverge by design (the oracle still checks the checkable arm where the
//! subset declines whole-declaration — each pins its oracle error plus one
//! unsupported note with its distinct reason): `ternary-return-nested-declined`
//! and `ternary-return-complex-declined`. Baselines keep diagnostic headers
//! only: tsc elaborates const-position unions with an indented detail line
//! that the header-only differential (and the solver's first-line message
//! contract) excludes — see the check-const P051 section.

use pith_frontend::{
    parse_module, CastFact as FrontendCastFact, CastKind as FrontendCastKind,
    CastOperandKind as FrontendCastOperandKind, EffectCallFact as FrontendEffectCall,
    FunctionBodyFact, FunctionFact as FrontendFunction, InitKind as FrontendInitKind,
    InnerDeclFact as FrontendInnerDecl, ParsedFile, ReturnKind as FrontendReturnKind,
    SingleReturnFact as FrontendReturn, TernaryArmFact as FrontendTernaryArm,
    TernaryFact as FrontendTernary,
};
use pith_ids::{FileId, Span, SymbolId};
use pith_queries::QueryDb;
use pith_solver::{
    check_functions, CastInput, CastKind, CountedForBody, DeclKind, EffectCall, ElseIfChainBody,
    FileReport, FunctionBody, FunctionDecl, FunctionParam, FunctionReturn, GuardChainBody,
    GuardEffectBody, GuardThrowBody, InitKind, InnerDecl, JoinedReturns, ObjectInit,
    ObjectMemberInit, ObjectMemberKind, StraightBody, StraightThrowBody, SwitchBody, TernaryArm,
    TernaryInit, TryCatchBody,
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
/// The boolean payload is dropped here (widened spells); member facts keep
/// it via [`map_member_kind`]. Exhaustive so a new frontend variant fails
/// to compile instead of silently mis-checking.
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

/// Maps one frontend return expression to the solver's return shape.
///
/// Object returns become member facts (always fresh: only direct syntactic
/// literals carry them); assertion returns carry their cast fact through
/// (no existing fixture holds one — zero differential effect, mapped so
/// the straight-body tail shares one faithful path). Every other return
/// becomes its literal kind. Exhaustive through
/// [`map_return_kind`]/[`map_member_kind`], so a new frontend variant fails
/// to compile instead of silently mis-checking.
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
        // Bare-identifier tails stay `None` here: only guard-effect tails
        // resolve through P048 (see `map_ident_tail`), so every other
        // position keeps its historical non-literal path.
        init_ident: None,
        init_object,
        // No array-member facts yet (adapter classifies `[ ... ]` as
        // non-literal): array returns decline in `shape_return` until the
        // adapter emits them.
        init_array: None,
        cast: ret.cast.as_ref().map(map_cast),
        // Ternary shapes ride without identifier names here (see
        // `map_ternary_return`): join legs never slice bare, so they keep
        // the historical whole-declaration non-literal decline.
        ternary: ret
            .ternary
            .as_ref()
            .map(|ternary| map_ternary(ternary, None)),
    }
}

/// Maps one frontend ternary arm to the solver's (P051): kind through the
/// widened [`map_return_kind`], span verbatim from facts, the nested flag
/// verbatim, and — only with a source text — the P048 seam for
/// bare-identifier arms (top-level single returns feed `Some`; join legs
/// feed `None` and decline instead of expanding).
fn map_ternary_arm(arm: &FrontendTernaryArm, source: Option<&str>) -> TernaryArm {
    let kind = map_return_kind(arm.kind);
    let bare = kind == InitKind::NonLiteral && !arm.is_conditional;
    let init_ident = if bare {
        source
            .and_then(|text| slice_of(text, arm.span))
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
fn map_ternary(ternary: &FrontendTernary, source: Option<&str>) -> TernaryInit {
    TernaryInit {
        then_arm: map_ternary_arm(&ternary.then_arm, source),
        else_arm: map_ternary_arm(&ternary.else_arm, source),
    }
}

/// Maps one top-level ternary return to the solver's (P051): the literal
/// shape through [`map_function_return`] plus the P048 seam per arm, so
/// bare-identifier arms resolve one level in [`check_one`].
fn map_ternary_return(source: &str, ret: &FrontendReturn) -> FunctionReturn {
    let mut mapped = map_function_return(ret);
    if let Some(ternary) = ret.ternary.as_ref() {
        mapped.ternary = Some(map_ternary(ternary, Some(source)));
    }
    mapped
}

/// Maps one frontend guard-effect tail to the solver's: the literal shape
/// through [`map_function_return`] plus the P048 seam for bare-identifier
/// tails (mirrors [`map_inner_decl`]: the adapter emits no identifier facts
/// for returns either, so the name slices from the return span — bare
/// identifiers only, so parenthesized idents keep the historical decline).
fn map_ident_tail(source: &str, ret: &FrontendReturn) -> FunctionReturn {
    let mut mapped = map_function_return(ret);
    let bare = mapped.kind == Some(InitKind::NonLiteral)
        && mapped.init_object.is_none()
        && mapped.cast.is_none();
    if bare {
        mapped.init_ident = slice_of(source, ret.span)
            .filter(|text| is_bare_identifier(text))
            .map(str::to_owned);
    }
    mapped
}

/// Maps one frontend guard chain body to the solver's: one return per guard
/// in source order plus the terminal return, each through
/// [`map_function_return`] (same `init_array: None` seam as every other
/// return position).
fn map_guard_chain(guards: &[FrontendReturn], tail: &FrontendReturn) -> GuardChainBody {
    GuardChainBody {
        guards: guards.iter().map(map_function_return).collect(),
        tail: map_function_return(tail),
    }
}

/// Maps one frontend effect call to the solver's: names cross as facts
/// (never sliced text), the count copies over; the solver allowlists.
fn map_effect_call(call: &FrontendEffectCall) -> EffectCall {
    EffectCall {
        receiver: call.receiver.clone(),
        member: call.member.clone(),
        arg_count: call.arg_count,
    }
}

/// Maps one joined frontend return pair to the solver's joined shape.
fn map_joined(first: &FrontendReturn, second: &FrontendReturn) -> JoinedReturns {
    JoinedReturns {
        first: map_function_return(first),
        second: map_function_return(second),
    }
}

/// Maps one frontend cast-operand kind to the solver's initializer kind.
///
/// Exhaustive so a new frontend variant fails to compile instead of
/// silently mis-checking (mirrors the check-any driver's cast map).
fn map_cast_operand_kind(kind: FrontendCastOperandKind) -> InitKind {
    match kind {
        FrontendCastOperandKind::Number => InitKind::Number,
        FrontendCastOperandKind::String => InitKind::String,
        FrontendCastOperandKind::Boolean => InitKind::Boolean,
        FrontendCastOperandKind::Null => InitKind::Null,
        FrontendCastOperandKind::Undefined => InitKind::Undefined,
        FrontendCastOperandKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend assertion form to the solver's, variant by variant.
///
/// Exhaustive so a new frontend variant fails to compile instead of silently
/// mis-checking (mirrors the check-any driver's cast map).
fn map_cast_kind(kind: FrontendCastKind) -> CastKind {
    match kind {
        FrontendCastKind::As => CastKind::As,
        FrontendCastKind::Satisfies => CastKind::Satisfies,
        FrontendCastKind::Angle => CastKind::Angle,
    }
}

/// Maps one frontend cast fact to the solver's input.
///
/// An unsliceable target (only possible with recovery from parse errors)
/// echoes as `""`, which the solver declines as complex — recorded, never
/// mis-checked or dropped (mirrors the check-any driver's cast map).
fn map_cast(cast: &FrontendCastFact) -> CastInput {
    CastInput {
        operand: map_cast_operand_kind(cast.operand_kind),
        target: cast.target_text.clone().unwrap_or_default(),
        operand_span: cast.operand_span,
        kind: map_cast_kind(cast.kind),
    }
}

/// Maps one frontend leading-initializer kind to the solver's.
///
/// Exhaustive so a new frontend variant fails to compile instead of
/// silently mis-checking.
fn map_inner_init_kind(kind: FrontendInitKind) -> InitKind {
    match kind {
        FrontendInitKind::Number => InitKind::Number,
        FrontendInitKind::String => InitKind::String,
        FrontendInitKind::Boolean => InitKind::Boolean,
        FrontendInitKind::Null => InitKind::Null,
        FrontendInitKind::Undefined => InitKind::Undefined,
        FrontendInitKind::NonLiteral => InitKind::NonLiteral,
    }
}

/// Maps one frontend leading declarator to the solver's straight-body
/// position.
///
/// Identity resolves through the binder from the fact's own symbol linkage
/// (mirroring [`fallback_span`]); object initializers become member facts
/// (always fresh); assertion initializers carry their cast fact through.
/// `init_ident` is the P048 seam (mirrors the check-const driver):
/// bare-identifier initializer names slice from the init fact span.
fn map_inner_decl(
    parsed: &ParsedFile,
    binder: &Binder,
    inner: &FrontendInnerDecl,
    source: &str,
) -> InnerDecl {
    let (name, span, symbol) = fallback_span(parsed, binder, inner.symbol, inner.scope);
    let init_object = inner.members.as_ref().map(|members| ObjectInit {
        members: members
            .iter()
            .map(|member| ObjectMemberInit {
                name: member.name.clone(),
                kind: map_member_kind(member.kind),
            })
            .collect(),
        fresh: true,
    });
    let init = if init_object.is_some() {
        None
    } else {
        inner
            .init
            .as_ref()
            .map(|init| map_inner_init_kind(init.kind))
    };
    let init_ident = match &inner.init {
        Some(init) if init.kind == FrontendInitKind::NonLiteral && init_object.is_none() => {
            slice_of(source, init.span)
                .filter(|text| is_bare_identifier(text))
                .map(str::to_owned)
        }
        _ => None,
    };
    InnerDecl {
        name,
        span,
        scope: inner.scope,
        symbol,
        kind: if inner.is_let {
            DeclKind::Let
        } else {
            DeclKind::Const
        },
        annotation: inner.annotation.as_ref().map(|ann| ann.text.clone()),
        init,
        init_ident,
        init_object,
        // No array-member facts yet (see `map_function_return`).
        init_array: None,
        cast: inner
            .init
            .as_ref()
            .and_then(|init| init.cast.as_ref())
            .map(map_cast),
    }
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
            .all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// Maps one frontend straight body to the solver's: leading declarators in
/// source order plus the terminal return.
fn map_straight(
    parsed: &ParsedFile,
    binder: &Binder,
    leading: &[FrontendInnerDecl],
    tail: &FrontendReturn,
    source: &str,
) -> StraightBody {
    StraightBody {
        leading: leading
            .iter()
            .map(|inner| map_inner_decl(parsed, binder, inner, source))
            .collect(),
        tail: map_function_return(tail),
    }
}

/// Maps one frontend try/catch body to the solver's: one return per arm
/// plus the optional trailing return, each through [`map_function_return`]
/// (array returns keep the shared `init_array: None` seam, so they ride
/// the same non-literal decline as every other return position).
fn map_try_catch(
    try_branch: &FrontendReturn,
    catch_branch: &FrontendReturn,
    tail: Option<&FrontendReturn>,
) -> TryCatchBody {
    TryCatchBody {
        try_branch: map_function_return(try_branch),
        catch_branch: map_function_return(catch_branch),
        tail: tail.map(map_function_return),
    }
}

/// Maps one frontend switch body to the solver's: one return per case in
/// source order plus the optional default return, each through
/// [`map_function_return`] (same `init_array: None` seam as every other
/// return position).
fn map_switch(cases: &[FrontendReturn], default: Option<&FrontendReturn>) -> SwitchBody {
    SwitchBody {
        cases: cases.iter().map(map_function_return).collect(),
        default: default.map(map_function_return),
    }
}

/// Maps one frontend counted-`for` body to the solver's: the loop-body
/// return plus the optional trailing return, each through
/// [`map_function_return`] (same `init_array: None` seam as every other
/// return position).
fn map_counted_for(body: &FrontendReturn, tail: Option<&FrontendReturn>) -> CountedForBody {
    CountedForBody {
        body: map_function_return(body),
        tail: tail.map(map_function_return),
    }
}

/// Maps one frontend else-if chain body to the solver's: one return per
/// branch in source order, each through [`map_function_return`] (same
/// `init_array: None` seam as every other return position).
fn map_else_if(branches: &[FrontendReturn]) -> ElseIfChainBody {
    ElseIfChainBody {
        branches: branches.iter().map(map_function_return).collect(),
    }
}

/// Maps one frontend straight-with-throw body to the solver's: leading
/// declarators in source order plus the optional terminal return (throws
/// carry no facts — see the module-level P043 throw rules). The lone
/// `throw` is the empty, tail-less form.
fn map_straight_throw(
    parsed: &ParsedFile,
    binder: &Binder,
    leading: &[FrontendInnerDecl],
    tail: Option<&FrontendReturn>,
    source: &str,
) -> StraightThrowBody {
    StraightThrowBody {
        leading: leading
            .iter()
            .map(|inner| map_inner_decl(parsed, binder, inner, source))
            .collect(),
        tail: tail.map(map_function_return),
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

/// The fact-fed driver: every [`FunctionDecl`] field comes from adapter facts.
///
/// - `name`/`scope`/`symbol` via symbol linkage + binder resolution;
/// - `params` as names + annotated-ness verbatim, `params_complex` verbatim;
/// - `return_annotation` as the frontend's colon-stripped text verbatim;
/// - `body` mapped variant by variant; object returns become member facts
///   (always fresh: only direct syntactic literals carry them), assertion
///   positions carry casts, and straight bodies map leading declarators
///   plus the tail return through [`map_straight`].
///
/// Maps one frontend body fact to the solver's, faithfully (every field
/// from adapter facts; only the enum translation is driver-side). Split
/// out so `functions_from_facts` stays within the line budget.
fn map_body(
    func: &FrontendFunction,
    parsed: &ParsedFile,
    binder: &Binder,
    source: &str,
) -> FunctionBody {
    match &func.body {
        FunctionBodyFact::SingleReturn(ret) => {
            FunctionBody::SingleReturn(map_ternary_return(source, ret))
        }
        FunctionBodyFact::SequenceReturns { first, second } => {
            FunctionBody::SequenceReturns(map_joined(first, second))
        }
        FunctionBodyFact::GuardReturn { guard, tail } => {
            FunctionBody::GuardReturn(map_joined(guard, tail))
        }
        FunctionBodyFact::GuardChain { guards, tail } => {
            FunctionBody::GuardChain(map_guard_chain(guards, tail))
        }
        FunctionBodyFact::GuardChainUnsupported { reason } => FunctionBody::GuardChainUnsupported {
            reason: reason.clone(),
        },
        FunctionBodyFact::BranchReturns {
            then_branch,
            else_branch,
        } => FunctionBody::BranchReturns(map_joined(then_branch, else_branch)),
        FunctionBodyFact::StraightBody { leading, tail } => {
            FunctionBody::StraightBody(map_straight(parsed, binder, leading, tail, source))
        }
        FunctionBodyFact::TryCatch {
            try_branch,
            catch_branch,
            tail,
        } => FunctionBody::TryCatch(Box::new(map_try_catch(
            try_branch,
            catch_branch,
            tail.as_ref(),
        ))),
        FunctionBodyFact::Switch { cases, default } => {
            FunctionBody::Switch(map_switch(cases, default.as_ref()))
        }
        FunctionBodyFact::CountedFor { body, tail } => {
            FunctionBody::CountedFor(map_counted_for(body, tail.as_ref()))
        }
        FunctionBodyFact::ElseIfChain { branches } => {
            FunctionBody::ElseIfChain(map_else_if(branches))
        }
        FunctionBodyFact::ElseIfUnsupported { reason } => FunctionBody::ElseIfUnsupported {
            reason: reason.clone(),
        },
        FunctionBodyFact::GuardThrow { tail } => FunctionBody::GuardThrow(GuardThrowBody {
            tail: map_function_return(tail),
        }),
        FunctionBodyFact::EffectOnly { call } => FunctionBody::EffectOnly(map_effect_call(call)),
        FunctionBodyFact::GuardEffect { call, tail } => {
            FunctionBody::GuardEffect(GuardEffectBody {
                call: map_effect_call(call),
                tail: tail.as_ref().map(|ret| map_ident_tail(source, ret)),
            })
        }
        FunctionBodyFact::EffectUnsupported { reason } => FunctionBody::EffectUnsupported {
            reason: reason.clone(),
        },
        FunctionBodyFact::StraightThrow { leading, tail } => FunctionBody::StraightThrow(
            map_straight_throw(parsed, binder, leading, tail.as_ref(), source),
        ),
        FunctionBodyFact::TryUnsupported { reason } => FunctionBody::TryUnsupported {
            reason: reason.clone(),
        },
        FunctionBodyFact::LoopUnsupported { reason } => FunctionBody::LoopUnsupported {
            reason: reason.clone(),
        },
        FunctionBodyFact::SwitchUnsupported { reason } => FunctionBody::SwitchUnsupported {
            reason: reason.clone(),
        },
        FunctionBodyFact::NoBody { declared } => FunctionBody::NoBody {
            declared: *declared,
        },
        FunctionBodyFact::Empty => FunctionBody::Empty,
        FunctionBodyFact::Complex => FunctionBody::Complex,
    }
}

fn functions_from_facts(parsed: &ParsedFile, binder: &Binder, source: &str) -> Vec<FunctionDecl> {
    parsed
        .functions
        .iter()
        .map(|func| {
            let (name, span, symbol) = fallback_span(parsed, binder, func.symbol, func.scope);
            let body = map_body(func, parsed, binder, source);
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
                // No async fact yet (the adapter emits none): every fixture
                // here is non-async, so `false` changes nothing.
                is_async: false,
                has_type_params: !func.type_params.is_empty() || func.type_params_complex,
                return_annotation: func.return_annotation.as_ref().map(|ann| ann.text.clone()),
                body,
            }
        })
        .collect()
}

/// Runs the full real pipeline on one source text with a fresh binder and db.
fn run_pipeline(source: &str) -> (ParsedFile, FileReport) {
    let parsed = parse_module(FILE, "fixture.ts", source);
    let frontend_errors = &parsed.errors;
    assert!(
        parsed.errors.is_empty(),
        "frontend errors: {frontend_errors:?}"
    );
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder, source);
    let mut db = QueryDb::new();
    let report = check_functions(FILE, &decls, &binder, &mut db);
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
                include_str!(concat!("../../../corpus/check-functions/", $source)),
                include_str!(concat!("../../../corpus/check-functions/", $expected)),
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
    return_mismatch_matches_ts2322,
    "return-mismatch.ts",
    "return-mismatch.expected.txt",
    0
);
fixture_test!(
    unannotated_return_is_unsupported,
    "unannotated-return.ts",
    "unannotated-return.expected.txt",
    1
);
fixture_test!(
    multi_return_sequence_is_silent,
    "multi-return.ts",
    "multi-return.expected.txt",
    0
);
fixture_test!(
    branching_matches_ts2322,
    "branching.ts",
    "branching.expected.txt",
    0
);
fixture_test!(
    guard_return_matches_ts2322,
    "guard-return.ts",
    "guard-return.expected.txt",
    0
);
fixture_test!(
    guard_chain_clean_is_silent,
    "guard-chain-clean.ts",
    "guard-chain-clean.expected.txt",
    0
);
fixture_test!(
    guard_chain_wrong_guard_matches_ts2322,
    "guard-chain-wrong-guard.ts",
    "guard-chain-wrong-guard.expected.txt",
    0
);
fixture_test!(
    guard_chain_wrong_tail_matches_ts2322,
    "guard-chain-wrong-tail.ts",
    "guard-chain-wrong-tail.expected.txt",
    0
);
fixture_test!(
    void_effect_guard_ident_tail_matches_ts2322,
    "void-effect-guard-ident-tail.ts",
    "void-effect-guard-ident-tail.expected.txt",
    0
);
fixture_test!(
    two_returns_match_ts2322_twice,
    "two-returns.ts",
    "two-returns.expected.txt",
    0
);
fixture_test!(
    object_return_is_silent,
    "object-return.ts",
    "object-return.expected.txt",
    0
);
fixture_test!(
    straight_clean_is_silent,
    "straight-clean.ts",
    "straight-clean.expected.txt",
    0
);
fixture_test!(
    straight_inner_wrong_matches_ts2322,
    "straight-inner-wrong.ts",
    "straight-inner-wrong.expected.txt",
    0
);
fixture_test!(
    straight_tail_wrong_matches_ts2322,
    "straight-tail-wrong.ts",
    "straight-tail-wrong.expected.txt",
    0
);
fixture_test!(
    straight_both_wrong_matches_ts2322_twice,
    "straight-both-wrong.ts",
    "straight-both-wrong.expected.txt",
    0
);
fixture_test!(
    straight_nested_block_matches_ts2322,
    "straight-nested-block.ts",
    "straight-nested-block.expected.txt",
    0
);
fixture_test!(
    straight_object_inner_matches_ts2322,
    "straight-object-inner.ts",
    "straight-object-inner.expected.txt",
    0
);
fixture_test!(
    straight_unannotated_cast_matches_ts2352,
    "straight-unannotated-cast.ts",
    "straight-unannotated-cast.expected.txt",
    0
);
fixture_test!(
    try_clean_is_silent,
    "try-clean.ts",
    "try-clean.expected.txt",
    0
);
fixture_test!(
    try_try_wrong_matches_ts2322,
    "try-try-wrong.ts",
    "try-try-wrong.expected.txt",
    0
);
fixture_test!(
    try_catch_wrong_matches_ts2322,
    "try-catch-wrong.ts",
    "try-catch-wrong.expected.txt",
    0
);
fixture_test!(
    try_both_wrong_matches_ts2322_twice,
    "try-both-wrong.ts",
    "try-both-wrong.expected.txt",
    0
);
fixture_test!(
    try_tail_wrong_matches_ts2322,
    "try-tail-wrong.ts",
    "try-tail-wrong.expected.txt",
    0
);
fixture_test!(
    try_binding_unused_is_silent,
    "try-binding-unused.ts",
    "try-binding-unused.expected.txt",
    0
);
fixture_test!(
    switch_clean_is_silent,
    "switch-clean.ts",
    "switch-clean.expected.txt",
    0
);
fixture_test!(
    switch_case_wrong_matches_ts2322,
    "switch-case-wrong.ts",
    "switch-case-wrong.expected.txt",
    0
);
fixture_test!(
    switch_default_wrong_matches_ts2322,
    "switch-default-wrong.ts",
    "switch-default-wrong.expected.txt",
    0
);
fixture_test!(
    switch_two_wrong_matches_ts2322_twice,
    "switch-two-wrong.ts",
    "switch-two-wrong.expected.txt",
    0
);
fixture_test!(
    for_clean_is_silent,
    "for-clean.ts",
    "for-clean.expected.txt",
    0
);
fixture_test!(
    for_body_wrong_matches_ts2322,
    "for-body-wrong.ts",
    "for-body-wrong.expected.txt",
    0
);
fixture_test!(
    for_zero_trip_matches_ts2322,
    "for-zero-trip.ts",
    "for-zero-trip.expected.txt",
    0
);
fixture_test!(
    throw_guard_clean_is_silent,
    "throw-guard-clean.ts",
    "throw-guard-clean.expected.txt",
    0
);
fixture_test!(
    throw_guard_tail_wrong_matches_ts2322,
    "throw-guard-tail-wrong.ts",
    "throw-guard-tail-wrong.expected.txt",
    0
);
fixture_test!(
    throw_straight_clean_is_silent,
    "throw-straight-clean.ts",
    "throw-straight-clean.expected.txt",
    0
);
fixture_test!(
    throw_straight_inner_wrong_matches_ts2322,
    "throw-straight-inner-wrong.ts",
    "throw-straight-inner-wrong.expected.txt",
    0
);
fixture_test!(
    throw_straight_tail_wrong_matches_ts2322,
    "throw-straight-tail-wrong.ts",
    "throw-straight-tail-wrong.expected.txt",
    0
);
fixture_test!(
    throw_terminal_inner_wrong_matches_ts2322,
    "throw-terminal-inner-wrong.ts",
    "throw-terminal-inner-wrong.expected.txt",
    0
);
fixture_test!(
    throw_only_is_silent,
    "throw-only.ts",
    "throw-only.expected.txt",
    0
);
fixture_test!(
    void_effect_clean_is_silent,
    "void-effect-clean.ts",
    "void-effect-clean.expected.txt",
    0
);
fixture_test!(
    void_effect_guard_clean_is_silent,
    "void-effect-guard-clean.ts",
    "void-effect-guard-clean.expected.txt",
    0
);
fixture_test!(
    void_effect_guard_wrong_matches_ts2322,
    "void-effect-guard-wrong.ts",
    "void-effect-guard-wrong.expected.txt",
    0
);
fixture_test!(
    void_effect_guard_two_calls_is_unsupported,
    "void-effect-guard-two-calls.ts",
    "void-effect-guard-two-calls.expected.txt",
    1
);
fixture_test!(
    void_effect_guard_nonallowlist_is_unsupported,
    "void-effect-guard-nonallowlist.ts",
    "void-effect-guard-nonallowlist.expected.txt",
    1
);
fixture_test!(
    void_effect_guard_valued_return_is_unsupported,
    "void-effect-guard-valued-return.ts",
    "void-effect-guard-valued-return.expected.txt",
    1
);
fixture_test!(
    elseif_clean_is_silent,
    "elseif-clean.ts",
    "elseif-clean.expected.txt",
    0
);
fixture_test!(
    elseif_branch_wrong_matches_ts2322,
    "elseif-branch-wrong.ts",
    "elseif-branch-wrong.expected.txt",
    0
);
fixture_test!(
    elseif_two_wrong_matches_ts2322_twice,
    "elseif-two-wrong.ts",
    "elseif-two-wrong.expected.txt",
    0
);
fixture_test!(
    named_param_clean_is_silent,
    "named-param-clean.ts",
    "named-param-clean.expected.txt",
    0
);
fixture_test!(
    named_param_body_wrong_matches_ts2322,
    "named-param-body-wrong.ts",
    "named-param-body-wrong.expected.txt",
    0
);
fixture_test!(
    named_param_unused_is_silent,
    "named-param-unused.ts",
    "named-param-unused.expected.txt",
    0
);
fixture_test!(
    ternary_return_clean_is_silent,
    "ternary-return-clean.ts",
    "ternary-return-clean.expected.txt",
    0
);
fixture_test!(
    ternary_return_wrong_then_matches_ts2322,
    "ternary-return-wrong-then.ts",
    "ternary-return-wrong-then.expected.txt",
    0
);
fixture_test!(
    ternary_return_wrong_else_matches_ts2322,
    "ternary-return-wrong-else.ts",
    "ternary-return-wrong-else.expected.txt",
    0
);
fixture_test!(
    ternary_return_both_wrong_matches_ts2322_twice,
    "ternary-return-both-wrong.ts",
    "ternary-return-both-wrong.expected.txt",
    0
);
fixture_test!(
    ternary_return_ident_arm_checks_per_arm,
    "ternary-return-ident.ts",
    "ternary-return-ident.expected.txt",
    0
);

#[test]
fn ternary_return_nested_divergence_pins_ts2322() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS2322` at the inner wrong arm while the solver records one
    // unsupported note and stays silent — the subset joins one level only,
    // never a partial verdict over the checkable arm.
    let source = include_str!("../../../corpus/check-functions/ternary-return-nested-declined.ts");
    let expected =
        include_str!("../../../corpus/check-functions/ternary-return-nested-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
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
        report.unsupported[0].reason.contains("nested ternary"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn ternary_return_complex_arm_divergence_pins_ts2322() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS2322` at the wrong literal arm (the call arm checks clean) while
    // the solver records one unsupported note and stays silent — complex
    // arms decline whole-declaration, never a partial verdict.
    let source = include_str!("../../../corpus/check-functions/ternary-return-complex-declined.ts");
    let expected = include_str!(
        "../../../corpus/check-functions/ternary-return-complex-declined.expected.txt"
    );
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
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
        report.unsupported[0].reason.contains("non-literal"),
        "reason: {}",
        report.unsupported[0].reason
    );
}
fixture_test!(
    ternary_return_any_arm_checks_sibling,
    "ternary-return-any-arm.ts",
    "ternary-return-any-arm.expected.txt",
    0
);
fixture_test!(
    ternary_return_unknown_arm_matches_ts2322,
    "ternary-return-unknown-arm.ts",
    "ternary-return-unknown-arm.expected.txt",
    0
);
fixture_test!(
    ternary_return_never_arm_checks_sibling,
    "ternary-return-never-arm.ts",
    "ternary-return-never-arm.expected.txt",
    0
);

fixture_test!(
    straight_identifier_init_matches_ts2322,
    "straight-identifier-init.ts",
    "straight-identifier-init.expected.txt",
    0
);

#[test]
fn straight_let_init_divergence_pins_ts2322() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS2322` on the `let`-initialized inner declarator (it observes the
    // literal through the mutable binding) while the solver records one
    // unsupported note and stays silent — `let` bindings never propagate.
    let source = include_str!("../../../corpus/check-functions/straight-let-init-declined.ts");
    let expected =
        include_str!("../../../corpus/check-functions/straight-let-init-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'number' is not assignable to type 'string'.".to_owned()
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
        report.unsupported[0].reason.contains("'let' binding"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn unknown_param_propagates_like_literal() {
    // An `unknown`-annotated parameter checks like an `unknown` literal
    // (probe p18): `TS2322` spelling `unknown` at the use.
    expect_differential(
        "unknown_param_propagates_like_literal",
        "function f(uu: unknown): string {\n  const x: string = uu;\n  return \"s\";\n}\n",
        "inline.ts:TS2322: Type 'unknown' is not assignable to type 'string'.",
        0,
    );
}

#[test]
fn any_param_is_silent() {
    // An `any`-annotated parameter admits silently (probe p17, clean).
    expect_differential(
        "any_param_is_silent",
        "function f(au: any): string {\n  const x: string = au;\n  return \"s\";\n}\n",
        "",
        0,
    );
}

#[test]
fn shadowed_outer_const_loses_to_param() {
    // Scope-sensitivity end to end (probe p28): the use resolves to the
    // nearest binding (the parameter), so the outer const never leaks in.
    let source = "const n = \"s\";\nfunction f(n: number): number {\n  const x: string = n;\n\
         return 1;\n}\n";
    expect_differential(
        "shadowed_outer_const_loses_to_param",
        source,
        "inline.ts:TS2322: Type 'number' is not assignable to type 'string'.",
        0,
    );
}

#[test]
fn optional_param_declines() {
    // Optional parameters carry `| undefined` (probe p16), which
    // single-level propagation cannot spell: decline, never a forced
    // verdict. The oracle baseline holds a continuation line, so only the
    // header pair is pinned here.
    let source = "function f(b?: number): string {\n  const x: string = b;\n  return \"s\";\n}\n";
    let expected =
        "inline.ts:TS2322: Type 'number | undefined' is not assignable to type 'string'.\n\
          Type 'undefined' is not assignable to type 'string'.";
    let headers: Vec<(String, String)> = parse_baseline(expected)
        .into_iter()
        .filter(|line| line.0 == "TS2322")
        .collect();
    assert_eq!(
        headers,
        [(
            "TS2322".to_owned(),
            "Type 'number | undefined' is not assignable to type 'string'.".to_owned()
        )],
        "baseline pins the oracle header"
    );
    let (_, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1);
    assert!(
        report.unsupported[0].reason.contains("optional"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn forward_reference_in_function_declines() {
    // Uses only see earlier leadings (probe p22, where tsc spells TS2448
    // plus TS2454): the not-yet-declared source declines.
    let source =
        "function h(): number {\n  const x: number = later;\n  const later = 1;\n  return 1;\n}\n";
    let expected = "inline.ts:TS2448: Block-scoped variable 'later' used before its declaration.\n\
        inline.ts:TS2454: Variable 'later' is used before being assigned.";
    assert_eq!(
        parse_baseline(expected),
        [
            (
                "TS2448".to_owned(),
                "Block-scoped variable 'later' used before its declaration.".to_owned()
            ),
            (
                "TS2454".to_owned(),
                "Variable 'later' is used before being assigned.".to_owned()
            ),
        ],
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
            .contains("used before its declaration"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn cross_scope_const_declines() {
    // One function pass sees only its own leadings and params (probe p21,
    // where tsc checks the top-level const): the outer name declines
    // instead of leaking across scopes.
    let source = "const n = 1;\nfunction g(): number {\n  const x: string = n;\n  return 1;\n}\n";
    let expected = "inline.ts:TS2322: Type 'number' is not assignable to type 'string'.";
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'number' is not assignable to type 'string'.".to_owned()
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
            .contains("no checkable const declarator"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

/// Asserts a clean-oracle try/catch decline: the recorded baseline pins
/// the oracle side (no diagnostics), while the pipeline stays silent with
/// exactly one unsupported note carrying the recorded reason.
fn expect_clean_oracle_decline(name: &str, source: &str, expected: &str, reason: &str) {
    assert!(
        parse_baseline(expected).is_empty(),
        "{name}: oracle is clean on this decline"
    );
    let (_, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "{name}: diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1, "{name}: one decline note");
    assert_eq!(
        report.unsupported[0].reason, reason,
        "{name}: recorded reason"
    );
}

#[test]
fn for_while_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: a `while`
    // loop body is clean in tsc (only the counted `for` idiom admits —
    // probed 7.0.2 P041) while the solver records one unsupported note with
    // the frontend's recorded reason.
    expect_clean_oracle_decline(
        "for_while_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/for-while-declined.ts"),
        include_str!("../../../corpus/check-functions/for-while-declined.expected.txt"),
        "while loop is outside the subset",
    );
}

#[test]
fn for_complex_body_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: a
    // multi-statement loop body is clean in tsc (probed 7.0.2 P041) while
    // the solver records one unsupported note with the frontend's recorded
    // reason.
    expect_clean_oracle_decline(
        "for_complex_body_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/for-complex-body-declined.ts"),
        include_str!("../../../corpus/check-functions/for-complex-body-declined.expected.txt"),
        "non-straight counted-for body is outside the subset",
    );
}

#[test]
fn for_nonliteral_bound_declines_where_oracle_errors() {
    // By design the subset declines where the oracle errors: tsc checks the
    // body return against the annotation (`TS2322`) while the solver rides
    // the bound gate — whole-decl decline, zero diagnostics, no value-type
    // facts.
    let source = include_str!("../../../corpus/check-functions/for-nonliteral-bound-declined.ts");
    let expected =
        include_str!("../../../corpus/check-functions/for-nonliteral-bound-declined.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
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
        report.unsupported[0].reason, "non-literal bound in for loop is outside the subset",
        "recorded reason"
    );
}

/// Asserts a pipeline-only loop decline (no oracle file): the pipeline
/// stays silent with exactly one unsupported note carrying the recorded
/// reason.
fn expect_loop_decline(name: &str, source: &str, reason: &str) {
    let (_, report) = run_pipeline(source);
    assert!(
        report.diagnostics.is_empty(),
        "{name}: diagnostics: {:?}",
        report.diagnostics
    );
    assert_eq!(report.unsupported.len(), 1, "{name}: one decline note");
    assert_eq!(
        report.unsupported[0].reason, reason,
        "{name}: recorded reason"
    );
}

#[test]
fn for_break_body_declines_with_break_reason() {
    // A bare `break` body is clean in tsc (probed 7.0.2 P041) while the
    // subset declines with the break/continue reason — never the complex
    // one.
    expect_loop_decline(
        "for_break_body_declines_with_break_reason",
        "function stop(): number {\n  for (let i = 0; i < 3; i++) {\n\
         break;\n  }\n  return 2;\n}\n",
        "break/continue in counted-for body is outside the subset",
    );
}

#[test]
fn for_labelled_continue_declines_with_break_reason() {
    // Labels are the only value `break`/`continue` carry: a labelled
    // `continue` rides the same reason as the bare form.
    expect_loop_decline(
        "for_labelled_continue_declines_with_break_reason",
        "function skip(): number {\n  for (let i = 0; i < 3; i++) {\n\
         done: continue;\n  }\n  return 2;\n}\n",
        "break/continue in counted-for body is outside the subset",
    );
}

#[test]
fn for_infinite_declines_with_infinite_reason() {
    // `for(;;)` is clean in tsc with a clean body (probed 7.0.2 P041)
    // while the subset declines with the infinite-loop reason.
    expect_loop_decline(
        "for_infinite_declines_with_infinite_reason",
        "function spin(): number {\n  for (;;) {\n    return 1;\n  }\n}\n",
        "infinite for loop is outside the subset",
    );
}

#[test]
fn for_non_numeric_bound_declines_with_numeric_reason() {
    // A string init literal is outside the numeric-bound rule (const-eval
    // the subset refuses) — distinct from the non-literal reason.
    expect_loop_decline(
        "for_non_numeric_bound_declines_with_numeric_reason",
        "function text(): number {\n  for (let i = \"a\"; i < 3; i++) {\n\
         return 1;\n  }\n  return 2;\n}\n",
        "non-numeric bound in for loop is outside the subset",
    );
}

#[test]
fn for_stepped_update_declines_with_shape_reason() {
    // `i += 2` is outside the simple `++` idiom — the header-shape reason.
    expect_loop_decline(
        "for_stepped_update_declines_with_shape_reason",
        "function stepped(): number {\n  for (let i = 0; i < 10; i += 2) {\n\
         return 1;\n  }\n  return 2;\n}\n",
        "non-counted for loop shape is outside the subset",
    );
}

#[test]
fn for_loop_var_return_declines_through_non_literal_gate() {
    // By design the subset declines where the oracle checks: `return i`
    // over the loop variable classifies `NonLiteral` (the variable carries
    // no value facts — the loop-carried pinned gap), so the whole
    // declaration declines with the position-naming reason and zero
    // diagnostics.
    expect_loop_decline(
        "for_loop_var_return_declines_through_non_literal_gate",
        "function pick(): number {\n  for (let i = 0; i < 3; i++) {\n\
         return i;\n  }\n  return 2;\n}\n",
        "non-literal loop return in 'pick' is outside the subset",
    );
}

#[test]
fn for_tail_wrong_matches_ts2322() {
    // A clean loop body plus a wrong tail reports once at the tail: the
    // tail is another position (probed 7.0.2 P041 — probe `h`).
    let (_, report) = run_pipeline(
        "function total(): number {\n  for (let i = 0; i < 3; i++) {\n\
         return 1;\n  }\n  return \"oops\";\n}\n",
    );
    let actual: Vec<(String, String)> = report
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
    assert_eq!(
        actual,
        [(
            "TS2322".to_owned(),
            "Type 'string' is not assignable to type 'number'.".to_owned()
        )],
    );
    assert!(report.unsupported.is_empty());
}

#[test]
fn throw_complex_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: an `if/else`
    // with a throw branch is clean in tsc (probed 7.0.2 P043) while the
    // solver records one unsupported note with the complex-body reason —
    // throw positions outside guard-throw/straight shapes never verdict
    // partially.
    expect_clean_oracle_decline(
        "throw_complex_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/throw-complex-declined.ts"),
        include_str!("../../../corpus/check-functions/throw-complex-declined.expected.txt"),
        "complex body on 'branchThrow': control flow is outside the subset",
    );
}

#[test]
fn guard_chain_missing_tail_declines_where_oracle_errors_ts2366() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS2366` on the missing tail return (exhaustiveness needs a
    // declaration-completeness family the subset refuses — probed 7.0.2
    // P050) while the solver records one unsupported note and stays silent
    // — never a forced verdict, never a partial one over the guards.
    let source = include_str!("../../../corpus/check-functions/guard-chain-missing-tail.ts");
    let expected =
        include_str!("../../../corpus/check-functions/guard-chain-missing-tail.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2366".to_owned(),
            "Function lacks ending return statement and return type does not include \
            'undefined'."
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
    assert_eq!(
        report.unsupported[0].reason,
        "missing tail return after guard returns is outside the subset",
        "recorded reason"
    );
}

#[test]
fn guard_chain_interleaved_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: a `const`
    // between the guards is clean in tsc (probed 7.0.2 P050) while the
    // solver records one unsupported note with the interleaved reason —
    // never a partial verdict over the guards or the tail.
    let src = include_str!("../../../corpus/check-functions/guard-chain-interleaved-declined.ts");
    let expected = include_str!(
        "../../../corpus/check-functions/guard-chain-interleaved-declined.expected.txt"
    );
    expect_clean_oracle_decline(
        "guard_chain_interleaved_decline_pins_clean_oracle",
        src,
        expected,
        "non-guard statement between guard returns is outside the subset",
    );
}

#[test]
fn guard_chain_two_wrong_reports_twice() {
    // Positions check independently (probed 7.0.2 P050 probe `g`): a wrong
    // guard plus a wrong tail report twice, once per position.
    expect_differential(
        "guard_chain_two_wrong_reports_twice",
        "function chained(a: boolean, b: boolean): number {\n  if (a) return \"oops\";\n\
        if (b) return 2;\n  return \"bad\";\n}\n",
        "inline.ts:TS2322: Type 'string' is not assignable to type 'number'.\n\
        inline.ts:TS2322: Type 'string' is not assignable to type 'number'.",
        0,
    );
}

#[test]
fn elseif_missing_else_declines_where_oracle_errors_ts2366() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS2366` on the missing terminal `else` (exhaustiveness needs a
    // declaration-completeness family the subset refuses) while the solver
    // records one unsupported note and stays silent — never a forced
    // verdict, never a partial one over the checkable branches.
    let source = include_str!("../../../corpus/check-functions/elseif-missing-else.ts");
    let expected = include_str!("../../../corpus/check-functions/elseif-missing-else.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2366".to_owned(),
            "Function lacks ending return statement and return type does not include \
            'undefined'."
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
    assert_eq!(
        report.unsupported[0].reason, "missing else in else-if chain is outside the subset",
        "recorded reason"
    );
}

#[test]
fn elseif_nested_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: a chain
    // nested inside a branch needs flow facts (probed 7.0.2 P045) while the
    // solver records one unsupported note with the nested-chain reason.
    expect_clean_oracle_decline(
        "elseif_nested_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/elseif-nested-declined.ts"),
        include_str!("../../../corpus/check-functions/elseif-nested-declined.expected.txt"),
        "nested else-if chain is outside the subset",
    );
}

#[test]
fn elseif_complex_branch_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: a `throw`
    // branch inside a chain is clean in tsc (throws accept any value —
    // probed 7.0.2 P043/P045) while the solver records one unsupported note
    // with the complex-branch reason — never a partial verdict over the
    // remaining branches.
    expect_clean_oracle_decline(
        "elseif_complex_branch_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/elseif-complex-branch-declined.ts"),
        include_str!("../../../corpus/check-functions/elseif-complex-branch-declined.expected.txt"),
        "complex else-if branch is outside the subset",
    );
}

#[test]
fn switch_fallthrough_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: an empty
    // `case` falls through in tsc (probed 7.0.2 P040) while the solver
    // records one unsupported note with the frontend's recorded reason.
    expect_clean_oracle_decline(
        "switch_fallthrough_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/switch-fallthrough-declined.ts"),
        include_str!("../../../corpus/check-functions/switch-fallthrough-declined.expected.txt"),
        "fallthrough case is outside the subset",
    );
}

#[test]
fn switch_complex_case_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: extra
    // statements before a case return need flow facts (probed 7.0.2 P040)
    // while the solver records one unsupported note with the frontend's
    // recorded reason.
    expect_clean_oracle_decline(
        "switch_complex_case_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/switch-complex-case-declined.ts"),
        include_str!("../../../corpus/check-functions/switch-complex-case-declined.expected.txt"),
        "complex case is outside the subset",
    );
}

#[test]
fn try_finally_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: tsc checks
    // `finally` returns (probed 7.0.2 P039) while the solver records one
    // unsupported note with the frontend's recorded reason.
    expect_clean_oracle_decline(
        "try_finally_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/try-finally-declined.ts"),
        include_str!("../../../corpus/check-functions/try-finally-declined.expected.txt"),
        "finally clause is outside the subset",
    );
}

#[test]
fn try_throw_decline_pins_clean_oracle() {
    // By design the subset declines where the oracle is clean: a `throw`
    // arm is clean in tsc (probed 7.0.2 P039) while the solver records one
    // unsupported note with the frontend's recorded reason.
    expect_clean_oracle_decline(
        "try_throw_decline_pins_clean_oracle",
        include_str!("../../../corpus/check-functions/try-throw-declined.ts"),
        include_str!("../../../corpus/check-functions/try-throw-declined.expected.txt"),
        "throw statement in try arm is outside the subset",
    );
}

#[test]
fn try_binding_used_declines_through_non_literal_gate() {
    // By design the subset declines where the oracle errors: tsc types the
    // caught binding as `unknown` and reports `TS2322` on `return e`,
    // while the solver classifies the arm `NonLiteral` and rides the
    // existing position-naming gate — whole-decl decline, zero
    // diagnostics, no new facts.
    let source = include_str!("../../../corpus/check-functions/try-binding-used.ts");
    let expected = include_str!("../../../corpus/check-functions/try-binding-used.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS2322".to_owned(),
            "Type 'unknown' is not assignable to type 'number'.".to_owned()
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
            .contains("non-literal catch return"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn unannotated_param_divergence_pins_ts7006() {
    // By design the subset declines where the oracle errors: tsc reports
    // `TS7006` (implicit any under `--strict`) while the solver records one
    // unsupported note and stays silent.
    let source = include_str!("../../../corpus/check-functions/unannotated-param.ts");
    let expected = include_str!("../../../corpus/check-functions/unannotated-param.expected.txt");
    assert_eq!(
        parse_baseline(expected),
        [(
            "TS7006".to_owned(),
            "Parameter 'value' implicitly has an 'any' type.".to_owned()
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
            .contains("unannotated parameter"),
        "reason: {}",
        report.unsupported[0].reason
    );
}

#[test]
fn excluded_shapes_emit_no_facts_and_stay_silent() {
    // Arrows, function expressions, and methods are out of scope: bound
    // symbols, zero function facts, empty differential on both sides.
    let source = include_str!("../../../corpus/check-functions/excluded-shapes.ts");
    let expected = include_str!("../../../corpus/check-functions/excluded-shapes.expected.txt");
    assert!(
        parse_baseline(expected).is_empty(),
        "oracle is clean on excluded shapes"
    );
    let (parsed, report) = run_pipeline(source);
    assert!(
        !parsed.symbols.is_empty(),
        "excluded shapes still bind symbols"
    );
    assert!(
        parsed.functions.is_empty(),
        "no function facts for excluded shapes"
    );
    assert!(report.diagnostics.is_empty());
    assert!(report.unsupported.is_empty());
}

#[test]
fn pipeline_is_deterministic_across_runs() {
    let source = include_str!("../../../corpus/check-functions/return-mismatch.ts");
    let (_, first) = run_pipeline(source);
    let (_, second) = run_pipeline(source);
    assert_eq!(first, second);
}

#[test]
fn driver_maps_facts_without_hand_feeding() {
    // Guards the mapping itself: names from symbol linkage, params verbatim,
    // annotation text verbatim, return kinds per variant (boolean payload
    // preserved in members), identifier inits sliced from fact spans, spans
    // anchored to the file.
    let source = "function add(a: number, b): string {\n  return \"ok\";\n}\n\
         function point(): { x: number; done: boolean } {\n  return { x: 1, done: false };\n}\n";
    let parsed = parse_module(FILE, "m.ts", source);
    let errors = &parsed.errors;
    assert!(parsed.errors.is_empty(), "errors: {errors:?}");
    assert_eq!(parsed.functions.len(), 2);
    let binder = build_binder(&parsed);
    let decls = functions_from_facts(&parsed, &binder, source);
    assert_eq!(decls.len(), 2);
    assert_eq!(decls[0].name, "add");
    assert_eq!(decls[0].return_annotation.as_deref(), Some("string"));
    let FunctionBody::SingleReturn(first_return) = &decls[0].body else {
        panic!("expected single return, got {:?}", decls[0].body);
    };
    assert_eq!(first_return.kind, Some(InitKind::String));
    assert!(first_return.init_object.is_none());
    assert!(decls[0].symbol.is_some(), "driver resolves the SymbolId");
    assert_eq!(
        decls[0].scope,
        parsed.symbols[usize::try_from(parsed.functions[0].symbol).expect("dense")].scope
    );
    let param_names: Vec<&str> = decls[0]
        .params
        .iter()
        .map(|param| param.name.as_str())
        .collect();
    assert_eq!(param_names, ["a", "b"]);
    assert_eq!(
        decls[0]
            .params
            .iter()
            .map(|param| param.annotated)
            .collect::<Vec<bool>>(),
        [true, false]
    );
    // Call-checker enabling rides along verbatim: annotation text plus
    // optional/rest markers.
    let param_texts: Vec<Option<&str>> = decls[0]
        .params
        .iter()
        .map(|param| param.annotation.as_deref())
        .collect();
    assert_eq!(param_texts, [Some("number"), None]);
    assert!(
        !decls[0]
            .params
            .iter()
            .any(|param| param.optional || param.is_rest),
        "plain params carry no markers"
    );
    assert_eq!(decls[1].name, "point");
    for decl in &decls {
        assert_eq!(decl.span.file, FILE);
        assert!(decl.span.lo < decl.span.hi);
    }
    let FunctionBody::SingleReturn(ret) = &decls[1].body else {
        panic!("expected single return, got {:?}", decls[1].body);
    };
    assert_eq!(ret.kind, None);
    let init = ret.init_object.as_ref().expect("object members");
    assert!(init.fresh);
    let members: Vec<(&str, ObjectMemberKind)> = init
        .members
        .iter()
        .map(|member| (member.name.as_str(), member.kind))
        .collect();
    assert_eq!(
        members,
        [
            ("x", ObjectMemberKind::Number),
            ("done", ObjectMemberKind::Boolean(false))
        ]
    );
}
