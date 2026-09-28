# Contributing to Pith

Pith keeps a fine-grained public history: many small atomic commits, each one
logical unit (a fact schema, a query, a test, a single fix, a lockfile regen).

- Each commit should build green on its own where feasible (`cargo fmt --check`,
  `cargo clippy --workspace --all-targets -- -D warnings`, `cargo test --workspace`
  on Linux; local Windows `cargo` execution is not used by this project).
- Commit messages are product-focused, one line, no agent vocabulary,
  no `Co-authored-by` trailers.
- Corrections are new commits; published history is append-only.
