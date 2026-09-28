# Benchmark methodology

Correctness gates performance. Never claim speed for a semantically divergent case.

Measure: cold check, warm check, one-char edit -> correct diagnostics,
repeated semantic query, peak RSS, CPU, 1/2/4/8-core scaling, invalidation size,
cache hit/miss.

Every claim records: Pith commit, competitor version, hardware, corpus, command,
semantic-equivalence gate, raw data.
