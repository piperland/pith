# Pith

> A persistent TypeScript semantic engine written in Rust.
> Part of [Piper — No-BS Dev Tools](https://github.com/piperland).

Pith's thesis: TypeScript semantics as a persistent, query-driven semantic
system with stable identities, shared semantic state, precise dependency
tracking and fine-grained invalidation.

A `tsc`-compatible checker is an important client of that engine, not the
architecture itself.

## Status

Early architecture phase. See `docs/` for compatibility status, architecture,
and benchmark methodology once the first primitives land.

## What works

Nothing yet — workspace initialized, first semantic primitives in progress.

## Layout

```text
crates/      # Rust workspace (earned boundaries only)
docs/        # architecture, compatibility, bench methodology
corpus/      # pinned fixtures (small, public-safe)
```

Internal autonomous-engineering mechanics (`.agent/`, `.opencode/`) are local
only and never enter this repository.

## Reproduce

All Rust execution happens on Linux (Deepnote Cloud preferred, E2B fallback).
Native Windows `cargo` execution is forbidden by project policy.

```sh
cargo test
cargo clippy -- -D warnings
```

## License

TBD — founder to choose before first external contribution.
