// Solver verdict: clean oracle + 2 UNSUPPORTED (nested object member type,
// optional member). Never silent, never forced.
const nested: { inner: { x: number } } = { inner: { x: 1 } };
const maybe: { a?: number } = {};
