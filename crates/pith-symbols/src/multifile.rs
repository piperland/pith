//! Cross-file module resolution: import specifiers to [`FileId`]s, imports to
//! declaring files.
//!
//! The [`ModuleGraph`] binds one program's per-file module facts (adapted by
//! drivers from the frontend's import/export facts — this crate never imports
//! `pith-frontend`, mirroring the [`Binder`] boundary) into a specifier graph
//! over fixture-local relative paths. [`ModuleGraph::resolve_import`] walks
//! named re-export chains and `export *` barrels transitively; anything it
//! cannot spell (default/namespace imports, namespace re-exports, ambiguous
//! stars, cycles, non-relative specifiers) declines as [`ImportError`] with a
//! reason, never silently.
//!
//! Path model: drivers assign each file an opaque slash-separated path (the
//! `path_hint` given to parsing, e.g. `"main.ts"`, `"sub/index.ts"`).
//! Resolution joins the importer's directory with the specifier, clamps
//! `..` at the root, and probes `as-is`, `+.ts`/`.tsx`, and
//! `/index.ts`/`.tsx` in order. Only `./` and `../` specifiers resolve:
//! bare (`lodash`), scoped (`@org/x`), absolute (`/x`), and `tsconfig-paths`
//! aliases are external-package or configured resolution —
//! `oxc_resolver` is absent from `Cargo.lock`, and hand-rolled relative
//! resolution is ~30 lines with zero new dependencies for a fixture-local
//! graph whose semantics we explicitly exclude. Explicit `.ts` suffixes
//! resolve leniently when the file exists (tsc's `TS5097` rejects them
//! without `allowImportingTsExtensions` — a pinned superset, never a wrong
//! verdict: resolution succeeding where tsc errors only ever *adds* checking
//! the oracle skips).
//!
//! [`Binder`]: super::Binder

use std::collections::{HashMap, HashSet};

use pith_ids::FileId;

/// Which exported name an import binding asks its target module for.
///
/// Driver-mapped from the frontend's import facts (mechanical copy).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportedName {
    /// `import { A as B }`: the name `A` in the target module.
    Named(String),
    /// `import D from`: the default export (outside the subset).
    Default,
    /// `import * as ns from`: the module namespace (outside the subset).
    Namespace,
}

/// One import binding of one module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportInput {
    /// Local name as written.
    pub local: String,
    /// Requested name in the target module.
    pub imported: ImportedName,
    /// Module specifier as written.
    pub specifier: String,
}

/// One locally-declared exported name of one module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalExportInput {
    /// Name visible to importers.
    pub exported: String,
    /// Local binding name.
    pub local: String,
}

/// One re-export of one module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReExportInput {
    /// Name visible to importers; `None` for `export *`.
    pub exported: Option<String>,
    /// Requested name in the target module; `None` for `export *` and for
    /// `export * as ns` (a namespace object: outside the subset).
    pub imported: Option<String>,
    /// Module specifier as written.
    pub specifier: String,
}

/// One module's facts for the graph, adapted by drivers from frontend facts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleInput {
    /// File identity (stable across edits — the persistent thesis).
    pub file: FileId,
    /// Opaque slash-separated path (`"main.ts"`, `"sub/index.ts"`).
    pub path: String,
    /// Import bindings in source order.
    pub imports: Vec<ImportInput>,
    /// Locally-declared exported names in source order.
    pub local_exports: Vec<LocalExportInput>,
    /// Re-exports in source order (named before star is a driver choice).
    pub reexports: Vec<ReExportInput>,
}

/// Where an imported name is declared: its file plus its local binding name
/// there. Callers look the binding up by name in the declaring file's facts —
/// import bindings are distinct symbols per file by design, so no
/// [`SymbolId`](super::SymbolId) ever crosses a file boundary here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedExport {
    /// File declaring the binding.
    pub file: FileId,
    /// Binding name in the declaring file.
    pub local: String,
}

/// Why an import did not resolve to a declaring file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportError {
    /// No import binding bears the local name (driver skew — the solver only
    /// asks about names from its import list).
    UnknownLocal {
        /// Local name asked for.
        name: String,
    },
    /// A default import: value/type shape unknowable without default-export
    /// facts (outside the subset).
    DefaultImport {
        /// Local name asked for.
        name: String,
    },
    /// A namespace import: member accesses need expression facts (outside
    /// the subset).
    NamespaceImport {
        /// Local name asked for.
        name: String,
    },
    /// The specifier resolves to no graph file.
    UnresolvableSpecifier {
        /// Specifier as written.
        specifier: String,
        /// Whether it was relative (`./`, `../`): non-relative specifiers
        /// are external packages or configured aliases (outside the subset),
        /// relative ones name a missing fixture-local file.
        relative: bool,
    },
    /// The target module exports no such member (oracle `TS2305`).
    NotExported {
        /// Module asked.
        file: FileId,
        /// Member name asked for.
        name: String,
    },
    /// Several `export *` barrels provide the name (tsc excludes conflicting
    /// stars; picking one would be speculation).
    Ambiguous {
        /// Member name asked for.
        name: String,
    },
    /// A re-export cycle names the member again (no fixpoint iteration in
    /// the subset).
    Cycle {
        /// Member name asked for.
        name: String,
    },
    /// An `export * as ns` namespace re-export (namespace objects need
    /// expression facts).
    NamespaceReexport {
        /// Exported namespace name.
        name: String,
    },
}

impl ImportError {
    /// The decline reason quoting this failure (recorded, never silent).
    #[must_use]
    pub fn reason(&self) -> String {
        match self {
            Self::UnknownLocal { name } => {
                format!("no import of '{name}': nothing to resolve")
            }
            Self::DefaultImport { name } => {
                format!("default import '{name}' is outside the subset")
            }
            Self::NamespaceImport { name } => {
                format!("namespace import '{name}' is outside the subset")
            }
            Self::UnresolvableSpecifier {
                specifier,
                relative,
            } => {
                if *relative {
                    format!(
                        "cannot resolve module '{specifier}': \
                         no such fixture-local file"
                    )
                } else {
                    format!(
                        "cannot resolve module '{specifier}': \
                         non-relative specifiers (node_modules, tsconfig-paths) \
                         are outside the subset"
                    )
                }
            }
            Self::NotExported { name, .. } => {
                format!("module exports no member '{name}'")
            }
            Self::Ambiguous { name } => {
                format!(
                    "multiple star exports provide '{name}': \
                     ambiguous re-exports are outside the subset"
                )
            }
            Self::Cycle { name } => {
                format!("re-export cycle at '{name}': outside the subset")
            }
            Self::NamespaceReexport { name } => {
                format!("namespace re-export '{name}' is outside the subset")
            }
        }
    }
}

/// Whether a specifier is resolved by the graph: `./` and `../` only.
#[must_use]
pub fn is_relative_specifier(specifier: &str) -> bool {
    specifier.starts_with("./")
        || specifier.starts_with("../")
        || specifier == "."
        || specifier == ".."
}

/// Joins an importer's path with a relative specifier, clamping `..` at the
/// root (segments past the root are dropped, never wrapped).
fn join_relative(importer_path: &str, specifier: &str) -> String {
    let mut parts: Vec<&str> = importer_path
        .rsplit_once('/')
        .map_or(Vec::new(), |(dir, _)| dir.split('/').collect());
    for segment in specifier.split('/') {
        match segment {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            name => parts.push(name),
        }
    }
    parts.join("/")
}

/// Candidate graph paths for one joined specifier, in probe order.
fn resolution_candidates(joined: &str) -> Vec<String> {
    vec![
        joined.to_owned(),
        format!("{joined}.ts"),
        format!("{joined}.tsx"),
        format!("{joined}/index.ts"),
        format!("{joined}/index.tsx"),
    ]
}

/// One program's import graph: path tables plus per-file module facts.
#[derive(Clone, Debug, Default)]
pub struct ModuleGraph {
    modules: HashMap<FileId, ModuleInput>,
    by_path: HashMap<String, FileId>,
}

impl ModuleGraph {
    /// Builds the graph from one program's module facts.
    ///
    /// Paths must be unique per driver contract; duplicates keep the first
    /// (deterministic for deterministic input, never a silent overwrite of
    /// the checked set).
    #[must_use]
    pub fn new(modules: Vec<ModuleInput>) -> Self {
        let mut graph = Self {
            modules: HashMap::new(),
            by_path: HashMap::new(),
        };
        for module in modules {
            if graph.modules.contains_key(&module.file) {
                continue;
            }
            graph
                .by_path
                .entry(module.path.clone())
                .or_insert(module.file);
            graph.modules.insert(module.file, module);
        }
        graph
    }

    /// The module facts for `file`, if present.
    #[must_use]
    pub fn module_of(&self, file: FileId) -> Option<&ModuleInput> {
        self.modules.get(&file)
    }

    /// All files in the graph, sorted by [`FileId`] (deterministic order).
    #[must_use]
    pub fn files(&self) -> Vec<FileId> {
        let mut files: Vec<FileId> = self.modules.keys().copied().collect();
        files.sort();
        files
    }

    /// Maps a relative specifier from `importer` to its target file.
    ///
    /// Returns `None` for non-relative specifiers and for relative ones
    /// naming no graph file.
    #[must_use]
    pub fn resolve_specifier(&self, importer: FileId, specifier: &str) -> Option<FileId> {
        if !is_relative_specifier(specifier) {
            return None;
        }
        let importer_path = self.modules.get(&importer)?.path.as_str();
        let joined = join_relative(importer_path, specifier);
        resolution_candidates(&joined)
            .iter()
            .filter_map(|candidate| self.by_path.get(candidate))
            .copied()
            .next()
    }

    /// Resolves an import binding to its declaring file and binding name.
    ///
    /// # Errors
    ///
    /// Returns [`ImportError`] when the binding is missing, default/namespace
    /// shaped, or its chain (specifiers, named re-exports, barrels) does not
    /// land on exactly one declaration.
    pub fn resolve_import(&self, file: FileId, local: &str) -> Result<ResolvedExport, ImportError> {
        let module = self
            .modules
            .get(&file)
            .ok_or_else(|| ImportError::UnknownLocal {
                name: local.to_owned(),
            })?;
        let entry = module
            .imports
            .iter()
            .find(|entry| entry.local == local)
            .ok_or_else(|| ImportError::UnknownLocal {
                name: local.to_owned(),
            })?;
        match &entry.imported {
            ImportedName::Default => Err(ImportError::DefaultImport {
                name: local.to_owned(),
            }),
            ImportedName::Namespace => Err(ImportError::NamespaceImport {
                name: local.to_owned(),
            }),
            ImportedName::Named(name) => {
                let Some(target) = self.resolve_specifier(file, &entry.specifier) else {
                    return Err(ImportError::UnresolvableSpecifier {
                        specifier: entry.specifier.clone(),
                        relative: is_relative_specifier(&entry.specifier),
                    });
                };
                self.resolve_export(target, name)
            }
        }
    }

    /// Resolves an exported member to its declaring file and binding name,
    /// walking named re-export chains and `export *` barrels transitively.
    ///
    /// # Errors
    ///
    /// Returns [`ImportError`] when the member is missing, ambiguous across
    /// barrels, cyclic, or namespace shaped.
    pub fn resolve_export(&self, file: FileId, name: &str) -> Result<ResolvedExport, ImportError> {
        self.export_in(file, name, &mut HashSet::new())
    }

    /// Transitive export walk with a visited set for cycle detection.
    fn export_in(
        &self,
        file: FileId,
        name: &str,
        visited: &mut HashSet<(FileId, String)>,
    ) -> Result<ResolvedExport, ImportError> {
        if !visited.insert((file, name.to_owned())) {
            return Err(ImportError::Cycle {
                name: name.to_owned(),
            });
        }
        let result = self.export_in_inner(file, name, visited);
        visited.remove(&(file, name.to_owned()));
        result
    }

    /// One export-resolution step: local declarations (following
    /// re-exported imports), then named re-exports, then star barrels.
    fn export_in_inner(
        &self,
        file: FileId,
        name: &str,
        visited: &mut HashSet<(FileId, String)>,
    ) -> Result<ResolvedExport, ImportError> {
        let module = self.modules.get(&file).ok_or(ImportError::NotExported {
            file,
            name: name.to_owned(),
        })?;
        if let Some(local) = module
            .local_exports
            .iter()
            .find(|entry| entry.exported == name)
            .map(|entry| entry.local.clone())
        {
            if module.imports.iter().any(|entry| entry.local == local) {
                // `import { X } …; export { X }`: the local binding is the
                // import itself — follow it (cycles guarded by `visited`).
                return self.import_in(file, &local, visited);
            }
            return Ok(ResolvedExport { file, local });
        }
        if let Some(found) = self.named_reexport(module, name, visited)? {
            return Ok(found);
        }
        self.star_reexport(file, module, name, visited)
    }

    /// Follows one import binding inside an export walk (re-exported
    /// imports); default/namespace bindings decline with their reasons.
    fn import_in(
        &self,
        file: FileId,
        local: &str,
        visited: &mut HashSet<(FileId, String)>,
    ) -> Result<ResolvedExport, ImportError> {
        let module = self.modules.get(&file).ok_or(ImportError::NotExported {
            file,
            name: local.to_owned(),
        })?;
        let entry = module
            .imports
            .iter()
            .find(|entry| entry.local == local)
            .ok_or(ImportError::NotExported {
                file,
                name: local.to_owned(),
            })?;
        match &entry.imported {
            ImportedName::Default => Err(ImportError::DefaultImport {
                name: local.to_owned(),
            }),
            ImportedName::Namespace => Err(ImportError::NamespaceImport {
                name: local.to_owned(),
            }),
            ImportedName::Named(name) => {
                let Some(target) = self.resolve_specifier(file, &entry.specifier) else {
                    return Err(ImportError::UnresolvableSpecifier {
                        specifier: entry.specifier.clone(),
                        relative: is_relative_specifier(&entry.specifier),
                    });
                };
                self.export_in(target, name, visited)
            }
        }
    }

    /// Named re-exports (`export { A as B } from`): first match wins;
    /// namespace markers (`export * as ns`) decline.
    fn named_reexport(
        &self,
        module: &ModuleInput,
        name: &str,
        visited: &mut HashSet<(FileId, String)>,
    ) -> Result<Option<ResolvedExport>, ImportError> {
        let Some(entry) = module
            .reexports
            .iter()
            .find(|entry| entry.exported.as_deref() == Some(name))
        else {
            return Ok(None);
        };
        let Some(imported) = entry.imported.as_deref() else {
            return Err(ImportError::NamespaceReexport {
                name: name.to_owned(),
            });
        };
        let Some(target) = self.resolve_specifier(module.file, &entry.specifier) else {
            return Err(ImportError::UnresolvableSpecifier {
                specifier: entry.specifier.clone(),
                relative: is_relative_specifier(&entry.specifier),
            });
        };
        self.export_in(target, imported, visited).map(Some)
    }

    /// Star barrels (`export * from`): exactly one distinct declaration wins;
    /// none is [`ImportError::NotExported`], several is
    /// [`ImportError::Ambiguous`]. Unresolvable star targets are skipped for
    /// hit collection but surface as [`ImportError::UnresolvableSpecifier`]
    /// when nothing else provides the name (tsc's `TS2307` at the star
    /// statement is the pinned gap: unused broken stars stay silent).
    fn star_reexport(
        &self,
        file: FileId,
        module: &ModuleInput,
        name: &str,
        visited: &mut HashSet<(FileId, String)>,
    ) -> Result<ResolvedExport, ImportError> {
        let mut hits: Vec<ResolvedExport> = Vec::new();
        let mut unresolvable: Option<ImportError> = None;
        for entry in module
            .reexports
            .iter()
            .filter(|entry| entry.exported.is_none() && entry.imported.is_none())
        {
            let Some(target) = self.resolve_specifier(module.file, &entry.specifier) else {
                unresolvable = unresolvable.or(Some(ImportError::UnresolvableSpecifier {
                    specifier: entry.specifier.clone(),
                    relative: is_relative_specifier(&entry.specifier),
                }));
                continue;
            };
            match self.export_in(target, name, visited) {
                Ok(hit) => {
                    if !hits.contains(&hit) {
                        hits.push(hit);
                    }
                }
                Err(ImportError::NotExported { .. }) => {}
                Err(other) => return Err(other),
            }
        }
        if hits.len() == 1 {
            Ok(hits.swap_remove(0))
        } else if hits.is_empty() {
            Err(unresolvable.unwrap_or(ImportError::NotExported {
                file,
                name: name.to_owned(),
            }))
        } else {
            Err(ImportError::Ambiguous {
                name: name.to_owned(),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(
        file: u32,
        path: &str,
        imports: Vec<ImportInput>,
        local_exports: Vec<(&str, &str)>,
        reexports: Vec<ReExportInput>,
    ) -> ModuleInput {
        ModuleInput {
            file: FileId(file),
            path: path.to_owned(),
            imports,
            local_exports: local_exports
                .into_iter()
                .map(|(exported, local)| LocalExportInput {
                    exported: exported.to_owned(),
                    local: local.to_owned(),
                })
                .collect(),
            reexports,
        }
    }

    fn named(local: &str, imported: &str, specifier: &str) -> ImportInput {
        ImportInput {
            local: local.to_owned(),
            imported: ImportedName::Named(imported.to_owned()),
            specifier: specifier.to_owned(),
        }
    }

    fn from(named_export: &str, imported: &str, specifier: &str) -> ReExportInput {
        ReExportInput {
            exported: Some(named_export.to_owned()),
            imported: Some(imported.to_owned()),
            specifier: specifier.to_owned(),
        }
    }

    fn star(specifier: &str) -> ReExportInput {
        ReExportInput {
            exported: None,
            imported: None,
            specifier: specifier.to_owned(),
        }
    }

    #[test]
    fn specifiers_resolve_relative_forms_only() {
        let graph = ModuleGraph::new(vec![
            module(0, "main.ts", vec![], vec![], vec![]),
            module(1, "shared.ts", vec![], vec![], vec![]),
            module(2, "sub/index.ts", vec![], vec![], vec![]),
            module(3, "sub/deep.ts", vec![], vec![], vec![]),
        ]);
        assert_eq!(
            graph.resolve_specifier(FileId(0), "./shared"),
            Some(FileId(1))
        );
        assert_eq!(
            graph.resolve_specifier(FileId(0), "./shared.ts"),
            Some(FileId(1))
        );
        assert_eq!(graph.resolve_specifier(FileId(0), "./sub"), Some(FileId(2)));
        assert_eq!(
            graph.resolve_specifier(FileId(3), "../shared"),
            Some(FileId(1))
        );
        assert_eq!(graph.resolve_specifier(FileId(0), "./missing"), None);
        assert_eq!(graph.resolve_specifier(FileId(0), "lodash"), None);
        assert_eq!(graph.resolve_specifier(FileId(0), "@/shared"), None);
        assert_eq!(graph.resolve_specifier(FileId(0), "/shared"), None);
        assert_eq!(
            graph
                .resolve_import(FileId(0), "anything")
                .expect_err("unknown local"),
            ImportError::UnknownLocal {
                name: "anything".to_owned()
            }
        );
    }

    #[test]
    fn named_chains_resolve_transitively() {
        let graph = ModuleGraph::new(vec![
            module(
                0,
                "main.ts",
                vec![named("L", "LIMIT", "./mid")],
                vec![],
                vec![],
            ),
            module(
                1,
                "mid.ts",
                vec![],
                vec![],
                vec![from("LIMIT", "LIMIT", "./shared")],
            ),
            module(2, "shared.ts", vec![], vec![("LIMIT", "LIMIT")], vec![]),
        ]);
        assert_eq!(
            graph.resolve_import(FileId(0), "L"),
            Ok(ResolvedExport {
                file: FileId(2),
                local: "LIMIT".to_owned()
            })
        );
    }

    #[test]
    fn barrels_resolve_and_conflicts_decline() {
        let graph = ModuleGraph::new(vec![
            module(
                0,
                "main.ts",
                vec![named("L", "LIMIT", "./index")],
                vec![],
                vec![],
            ),
            module(1, "index.ts", vec![], vec![], vec![star("./shared")]),
            module(2, "shared.ts", vec![], vec![("LIMIT", "LIMIT")], vec![]),
        ]);
        assert_eq!(
            graph.resolve_import(FileId(0), "L"),
            Ok(ResolvedExport {
                file: FileId(2),
                local: "LIMIT".to_owned()
            })
        );
        assert_eq!(
            graph.resolve_export(FileId(1), "NOPE"),
            Err(ImportError::NotExported {
                file: FileId(1),
                name: "NOPE".to_owned()
            })
        );
        let ambiguous = ModuleGraph::new(vec![
            module(
                0,
                "main.ts",
                vec![named("L", "LIMIT", "./index")],
                vec![],
                vec![],
            ),
            module(
                1,
                "index.ts",
                vec![],
                vec![],
                vec![star("./a"), star("./b")],
            ),
            module(2, "a.ts", vec![], vec![("LIMIT", "LIMIT")], vec![]),
            module(3, "b.ts", vec![], vec![("LIMIT", "LIMIT")], vec![]),
        ]);
        assert_eq!(
            ambiguous.resolve_import(FileId(0), "L"),
            Err(ImportError::Ambiguous {
                name: "LIMIT".to_owned()
            })
        );
    }

    #[test]
    fn cycles_and_shapes_decline_with_reasons() {
        let graph = ModuleGraph::new(vec![
            module(
                0,
                "main.ts",
                vec![
                    named("L", "X", "./a"),
                    ImportInput {
                        local: "D".to_owned(),
                        imported: ImportedName::Default,
                        specifier: "./a".to_owned(),
                    },
                    ImportInput {
                        local: "ns".to_owned(),
                        imported: ImportedName::Namespace,
                        specifier: "./a".to_owned(),
                    },
                ],
                vec![],
                vec![],
            ),
            module(1, "a.ts", vec![], vec![], vec![from("X", "X", "./b")]),
            module(2, "b.ts", vec![], vec![], vec![from("X", "X", "./a")]),
        ]);
        assert_eq!(
            graph.resolve_import(FileId(0), "L"),
            Err(ImportError::Cycle {
                name: "X".to_owned()
            })
        );
        assert_eq!(
            graph.resolve_import(FileId(0), "D"),
            Err(ImportError::DefaultImport {
                name: "D".to_owned()
            })
        );
        assert_eq!(
            graph.resolve_import(FileId(0), "ns"),
            Err(ImportError::NamespaceImport {
                name: "ns".to_owned()
            })
        );
        for name in ["L", "D", "ns"] {
            let reason = graph
                .resolve_import(FileId(0), name)
                .expect_err("declines")
                .reason();
            assert!(!reason.is_empty(), "reason for {name}");
        }
        assert_eq!(
            graph.resolve_import(FileId(0), "GONE"),
            Err(ImportError::UnknownLocal {
                name: "GONE".to_owned()
            })
        );
    }

    #[test]
    fn reexported_imports_follow_through() {
        let graph = ModuleGraph::new(vec![
            module(0, "main.ts", vec![named("L", "X", "./mid")], vec![], vec![]),
            module(
                1,
                "mid.ts",
                vec![named("X", "X", "./shared")],
                vec![("X", "X")],
                vec![],
            ),
            module(2, "shared.ts", vec![], vec![("X", "X")], vec![]),
        ]);
        assert_eq!(
            graph.resolve_import(FileId(0), "L"),
            Ok(ResolvedExport {
                file: FileId(2),
                local: "X".to_owned()
            })
        );
    }
}
