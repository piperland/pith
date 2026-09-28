// Solver verdict: clean oracle + 3 UNSUPPORTED (union member type, missing
// annotation, non-literal initializer). Never silent, never forced.
const uni: { a: number | string } = { a: 1 };
const bare = { a: 1 };
const source = { a: 1 };
const alias: { a: number } = source;
