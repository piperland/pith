// Solver verdict: UNSUPPORTED (identifier initializers carry no value-type
// facts, so the unknown flow cannot be checked; oracle TS2322 — pinned
// divergence, never a forced verdict).
declare const uv: unknown;
const a: string = uv;
