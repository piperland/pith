# Architecture

Target:

```text
.ts/.tsx -> frontend (Oxc default) -> FileId/NodeId/Span
-> binder -> SymbolStore/TypeStore/SignatureStore/ModuleStore
-> query engine (resolve/type_of/members_of/signatures_of/instantiate/is_assignable/diagnostics)
-> memoized results + explicit dependencies -> fine-grained invalidation
```

Invariants:
- Semantic entities addressed by stable copyable ids.
- One shared semantic world; multiple executors.
- Where TS requires contextual/provisional/speculative evaluation, scope it explicitly and record why global identity is unsafe.

Kill condition: tsgo-in-Rust with TypeId wrappers and no substantial
edit/query/memory/cold-check win means the thesis failed.
