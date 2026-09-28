# Corpus

- A: upstream conformance/regression (pinned TS tests)
- B: generated adversarial (conditionals, mapped, infer, literals, overloads, variance, ...)
- C: pinned real projects (exact revisions)
- D: performance torture (huge unions, deep conditionals, instantiation explosions, ...)

Small public-safe fixtures only. Large/private corpora stay local under `.agent/`.
