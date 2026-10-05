// Solver verdict: 1 UNSUPPORTED (a receiver naming a program binding never
// reads the known-global pairs - resolve-first shadowing guard; tsc spells
// `TS2339`, a pinned oracle-error divergence). The `export {}` keeps the
// shadowing module-scoped so the oracle stays a single use-site error.
const Object = 1;
const a: string[] = Object.keys({ x: 1 });
export {};
