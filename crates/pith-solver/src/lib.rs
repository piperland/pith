//! Pith const-declaration solver: first real semantic thread.
//!
//! Pipeline: caller-supplied [`ConstDecl`]s (one per `const` declarator)
//! resolve their declaration spans through the [`Binder`], map their
//! annotation names to [`TypeStore`] builtins, memoize one
//! [`QueryKind::TypeOf`] answer per declaration in the [`QueryDb`], and emit
//! [`PithDiagnostic`]s for contradictions. Diagnostics are sorted by
//! `(file, span.lo, span.hi)` so repeated runs agree byte-for-byte.
//!
//! Diagnostic code mapping (Pith verdict on the left, oracle on the right):
//!
//! - `PITH2322` <-> `TS2322`: initializer literal type is not assignable to
//!   the annotation type. Message mirrors tsc shape:
//!   `Type 'string' is not assignable to type 'number'.`
//! - `PITH2304` <-> `TS2304`: annotation names an unknown type. Message
//!   mirrors tsc shape: `Cannot find name 'Nope'.`
//!
//! Out-of-subset declarations (union annotations, missing annotations,
//! non-literal or missing initializers) are recorded as [`UnsupportedDecl`]
//! entries, never silently dropped.
//!
//! BLOCKER (P004 adapter gap): [`ConstDecl::annotation`] and
//! [`ConstDecl::init`] are stand-ins for the missing adapter facts
//! `DeclAnnotationFact` (annotation text + span) and `InitLiteralFact`
//! (initializer literal kind + span). `ParsedFile` v1
//! carries declaration spans only, so no implementation can recover these
//! from facts alone without string-searching source text, which is
//! forbidden. The corpus driver hand-feeds them per fixture — the same
//! hand-fed seam as M1's `compute` closures — until the adapter emits them.
//! Declaration spans themselves always come from the [`Binder`] when the
//! name is bound there; [`ConstDecl::span`] is only a fallback.
//!
//! Design law (H-002): literal freshness and every other per-occurrence
//! verdict lives in the [`QueryDb`] memo entries keyed by occurrence
//! ([`NodeId`]), never in [`TypeData`](pith_types::TypeData).

use pith_ids::{FileId, NodeId, Span, TypeId};
use pith_queries::{Dep, QueryDb, QueryKey, QueryKind};
use pith_symbols::Binder;
use pith_types::TypeStore;

/// Code for literal-vs-annotation contradictions (oracle `TS2322`).
pub const CODE_MISMATCH: &str = "PITH2322";
/// Code for unknown annotation names (oracle `TS2304`).
pub const CODE_UNKNOWN_ANNOTATION: &str = "PITH2304";

/// One solver verdict: machine-comparable code plus anchored span.
///
/// `file`/`span` always name a declaration span (never a string slice);
/// `message` mirrors the oracle wording for its code family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PithDiagnostic {
    /// `"PITH2322"`-style code; see [`CODE_MISMATCH`]/[`CODE_UNKNOWN_ANNOTATION`].
    pub code: String,
    /// File owning the diagnostic span.
    pub file: FileId,
    /// Declaration span the diagnostic points at.
    pub span: Span,
    /// Human wording, mirroring the oracle message for the code family.
    pub message: String,
}

/// A declaration the solver refuses to verdict, with the reason why.
///
/// Out-of-subset input lands here so it is recorded, never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnsupportedDecl {
    /// File owning the declaration.
    pub file: FileId,
    /// Declaration span (binder span when bound, caller span otherwise).
    pub span: Span,
    /// Why no verdict exists (e.g. `"union annotation 'number | string'"`).
    pub reason: String,
}

/// Full per-file verdict: sorted errors plus sorted unsupported notes.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FileReport {
    /// Error diagnostics, sorted by `(file, span.lo, span.hi)`.
    pub diagnostics: Vec<PithDiagnostic>,
    /// Out-of-subset notes, sorted by `(file, span.lo, span.hi)`.
    pub unsupported: Vec<UnsupportedDecl>,
}

/// Initializer shapes inside the solver subset.
///
/// Only primitive literals are classifiable. Anything else needs expression
/// facts the adapter does not emit yet, so it maps to [`InitKind::NonLiteral`]
/// and becomes an [`UnsupportedDecl`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitKind {
    /// A numeric literal (`1`, `0x10`, ...).
    Number,
    /// A string literal (`"ok"`, ...).
    String,
    /// `true` / `false`.
    Boolean,
    /// `null`.
    Null,
    /// `undefined`.
    Undefined,
    /// Any non-literal initializer (identifier, object, call, ...).
    NonLiteral,
}

impl InitKind {
    /// The builtin [`TypeId`] this literal inhabits.
    ///
    /// `NonLiteral` has no known type here, so it yields [`TypeStore::UNKNOWN`]
    /// and callers must route it to unsupported, never to a verdict.
    #[must_use]
    pub fn type_id(self) -> TypeId {
        match self {
            Self::Number => TypeStore::NUMBER,
            Self::String => TypeStore::STRING,
            Self::Boolean => TypeStore::BOOLEAN,
            Self::Null => TypeStore::NULL,
            Self::Undefined => TypeStore::UNDEFINED,
            Self::NonLiteral => TypeStore::UNKNOWN,
        }
    }

    /// The tsc-style type name used in diagnostic messages.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Number => "number",
            Self::String => "string",
            Self::Boolean => "boolean",
            Self::Null => "null",
            Self::Undefined => "undefined",
            Self::NonLiteral => "unknown",
        }
    }
}

/// One `const` declarator to check.
///
/// `annotation`/`init` are hand-fed stand-ins for the missing adapter facts
/// (see the module-level BLOCKER); `span` is a fallback used only when the
/// name is not bound in the [`Binder`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstDecl {
    /// Declared name, resolved through the [`Binder`] for its span.
    pub name: String,
    /// Fallback span when the name is absent from the [`Binder`].
    pub span: Span,
    /// Raw annotation text (`Some("number")`); `None` means unannotated.
    pub annotation: Option<String>,
    /// Initializer literal kind; `None` means no initializer.
    pub init: Option<InitKind>,
}

/// Maps a primitive annotation name to its builtin [`TypeId`].
///
/// Returns `None` for anything outside the six-name subset. Union text is
/// detected by callers via `'|'` before reaching this map, so `None` here
/// always means "unknown name" (diagnose), never "out of subset".
#[must_use]
pub fn annotation_type(name: &str) -> Option<TypeId> {
    match name.trim() {
        "number" => Some(TypeStore::NUMBER),
        "string" => Some(TypeStore::STRING),
        "boolean" => Some(TypeStore::BOOLEAN),
        "void" => Some(TypeStore::VOID),
        "undefined" => Some(TypeStore::UNDEFINED),
        "null" => Some(TypeStore::NULL),
        _ => None,
    }
}

/// Checks every declarator in `decls` for `file`, threading each annotated
/// declaration's type through `db` (one memoized [`QueryKind::TypeOf`] query
/// per declaration) and returning the sorted [`FileReport`].
///
/// Declaration spans prefer the [`Binder`]'s first-declaration span for the
/// name; the caller span in [`ConstDecl`] is a fallback only.
#[must_use]
pub fn check_file(
    file: FileId,
    decls: &[ConstDecl],
    binder: &Binder,
    db: &mut QueryDb,
) -> FileReport {
    let mut report = FileReport::default();
    for (index, decl) in decls.iter().enumerate() {
        check_one(file, index, decl, binder, db, &mut report);
    }
    report.diagnostics.sort_by(|left, right| {
        (left.file, left.span.lo, left.span.hi).cmp(&(right.file, right.span.lo, right.span.hi))
    });
    report.unsupported.sort_by(|left, right| {
        (left.file, left.span.lo, left.span.hi).cmp(&(right.file, right.span.lo, right.span.hi))
    });
    report
}

/// Saturating declaration index into the occurrence [`NodeId`] key.
///
/// The index is a placeholder occurrence identity until the adapter emits
/// real `NodeId` facts; saturation (never wrapping) keeps skewed inputs
/// from aliasing declaration zero.
fn occurrence_node(index: usize) -> NodeId {
    NodeId(u32::try_from(index).unwrap_or(u32::MAX))
}

/// First-declaration span for `name` in `file`, if the binder knows it.
fn binder_span(binder: &Binder, file: FileId, name: &str) -> Option<Span> {
    binder
        .store()
        .iter()
        .find(|symbol| symbol.file == file && symbol.name == name)
        .map(|symbol| symbol.span)
}

/// Checks one declarator, pushing into `report`.
fn check_one(
    file: FileId,
    index: usize,
    decl: &ConstDecl,
    binder: &Binder,
    db: &mut QueryDb,
    report: &mut FileReport,
) {
    let span = binder_span(binder, file, &decl.name).unwrap_or(decl.span);
    let Some(raw) = decl.annotation.as_deref() else {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "no annotation: inference is outside the subset".to_owned(),
        });
        return;
    };
    let annotation = raw.trim();
    if annotation.contains('|') {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: format!("union annotation '{annotation}' is outside the subset"),
        });
        return;
    }
    let Some(ann_ty) = annotation_type(annotation) else {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_UNKNOWN_ANNOTATION.to_owned(),
            file,
            span,
            message: format!("Cannot find name '{annotation}'."),
        });
        return;
    };
    // Thread through the memo database: the annotation type is the answer
    // to this declaration's TypeOf query; the dep edge lets a later edit
    // invalidate exactly this entry.
    let node = occurrence_node(index);
    let key = QueryKey {
        file,
        node,
        kind: QueryKind::TypeOf,
    };
    let dep = Dep { file, node };
    let stored = db.type_of(key, &[dep], || ann_ty);
    debug_assert_eq!(stored, ann_ty);
    let Some(init) = decl.init else {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "missing initializer: nothing to check against".to_owned(),
        });
        return;
    };
    if init == InitKind::NonLiteral {
        report.unsupported.push(UnsupportedDecl {
            file,
            span,
            reason: "non-literal initializer is outside the subset".to_owned(),
        });
        return;
    }
    if init.type_id() != ann_ty {
        report.diagnostics.push(PithDiagnostic {
            code: CODE_MISMATCH.to_owned(),
            file,
            span,
            message: format!(
                "Type '{}' is not assignable to type '{annotation}'.",
                init.name()
            ),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pith_symbols::{ScopeInput, SymbolInput};

    const FILE: FileId = FileId(0);

    fn span(lo: u32, hi: u32) -> Span {
        Span { file: FILE, lo, hi }
    }

    fn binder_with(names: &[(&str, Span)]) -> Binder {
        let mut binder = Binder::new();
        let symbols: Vec<SymbolInput> = names
            .iter()
            .map(|(name, decl_span)| SymbolInput {
                scope: 0,
                name: (*name).to_owned(),
                span: *decl_span,
                flags: 0,
            })
            .collect();
        binder.build_file(
            FILE,
            &[ScopeInput {
                index: 0,
                parent: u32::MAX,
            }],
            &symbols,
            &[],
        );
        binder
    }

    fn decl(name: &str, lo: u32, hi: u32, ann: &str, init: InitKind) -> ConstDecl {
        ConstDecl {
            name: name.to_owned(),
            span: span(lo, hi),
            annotation: Some(ann.to_owned()),
            init: Some(init),
        }
    }

    #[test]
    fn annotation_type_maps_six_primitives() {
        let cases = [
            ("number", TypeStore::NUMBER),
            ("string", TypeStore::STRING),
            ("boolean", TypeStore::BOOLEAN),
            ("void", TypeStore::VOID),
            ("undefined", TypeStore::UNDEFINED),
            ("null", TypeStore::NULL),
            ("  string  ", TypeStore::STRING),
        ];
        for (text, expected) in cases {
            assert_eq!(annotation_type(text), Some(expected), "annotation {text:?}");
        }
        for unknown in ["Nope", "number[]", "", "Number"] {
            assert_eq!(annotation_type(unknown), None, "annotation {unknown:?}");
        }
    }

    #[test]
    fn correct_subset_is_silent_and_memoized() {
        let binder = binder_with(&[("a", span(0, 10)), ("b", span(11, 21)), ("c", span(22, 32))]);
        let decls = [
            decl("a", 0, 10, "number", InitKind::Number),
            decl("b", 11, 21, "string", InitKind::String),
            decl("c", 22, 32, "boolean", InitKind::Boolean),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
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
        assert_eq!(db.recompute_count(), 3);
        // A second pass over the same declarations must hit the memo cache.
        let repeat = check_file(FILE, &decls, &binder, &mut db);
        assert!(repeat.diagnostics.is_empty());
        assert_eq!(db.recompute_count(), 3);
    }

    #[test]
    fn literal_mismatches_are_sorted_pith2322() {
        let binder = binder_with(&[("a", span(40, 50)), ("b", span(0, 10)), ("c", span(20, 30))]);
        // Caller order is scrambled; diagnostics must come out sorted by lo.
        let decls = [
            decl("a", 40, 50, "number", InitKind::String),
            decl("b", 0, 10, "string", InitKind::Number),
            decl("c", 20, 30, "boolean", InitKind::Number),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(report.unsupported.is_empty());
        let codes: Vec<&str> = report.diagnostics.iter().map(|d| d.code.as_str()).collect();
        assert_eq!(codes, [CODE_MISMATCH, CODE_MISMATCH, CODE_MISMATCH]);
        let los: Vec<u32> = report.diagnostics.iter().map(|d| d.span.lo).collect();
        assert_eq!(los, [0, 20, 40]);
        assert_eq!(
            report.diagnostics[0].message,
            "Type 'number' is not assignable to type 'string'."
        );
    }

    #[test]
    fn unknown_annotation_is_pith2304() {
        let binder = binder_with(&[("v", span(5, 15))]);
        let decls = [decl("v", 5, 15, "Nope", InitKind::Number)];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_UNKNOWN_ANNOTATION);
        assert_eq!(report.diagnostics[0].message, "Cannot find name 'Nope'.");
        assert_eq!(report.diagnostics[0].span, span(5, 15));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn out_of_subset_is_unsupported_never_silent() {
        let binder = binder_with(&[
            ("u", span(0, 8)),
            ("n", span(9, 17)),
            ("e", span(18, 26)),
            ("m", span(27, 35)),
        ]);
        let decls = [
            decl("u", 0, 8, "number | string", InitKind::Number),
            ConstDecl {
                name: "n".to_owned(),
                span: span(9, 17),
                annotation: None,
                init: Some(InitKind::Number),
            },
            decl("e", 18, 26, "number", InitKind::NonLiteral),
            ConstDecl {
                name: "m".to_owned(),
                span: span(27, 35),
                annotation: Some("number".to_owned()),
                init: None,
            },
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert!(
            report.diagnostics.is_empty(),
            "diagnostics: {:?}",
            report.diagnostics
        );
        assert_eq!(report.unsupported.len(), 4);
        let los: Vec<u32> = report.unsupported.iter().map(|u| u.span.lo).collect();
        assert_eq!(los, [0, 9, 18, 27]);
    }

    #[test]
    fn multi_declarator_mixed_verdicts() {
        let binder = binder_with(&[
            ("first", span(0, 12)),
            ("second", span(13, 27)),
            ("third", span(28, 42)),
        ]);
        let decls = [
            decl("first", 0, 12, "number", InitKind::Number),
            decl("second", 13, 27, "string", InitKind::String),
            decl("third", 28, 42, "boolean", InitKind::Number),
        ];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code, CODE_MISMATCH);
        assert_eq!(report.diagnostics[0].span, span(28, 42));
        assert!(report.unsupported.is_empty());
    }

    #[test]
    fn binder_span_wins_over_caller_fallback() {
        let binder = binder_with(&[("v", span(100, 110))]);
        // Caller span is a stale fallback; the verdict must point at the
        // real declaration span from the binder.
        let decls = [decl("v", 0, 5, "number", InitKind::String)];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(100, 110));
    }

    #[test]
    fn unbound_name_falls_back_to_caller_span() {
        let binder = binder_with(&[]);
        let decls = [decl("ghost", 7, 17, "string", InitKind::Number)];
        let mut db = QueryDb::new();
        let report = check_file(FILE, &decls, &binder, &mut db);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].span, span(7, 17));
    }
}
