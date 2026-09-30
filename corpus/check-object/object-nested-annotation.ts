// Solver verdict: clean oracle + 1 UNSUPPORTED (nested object member type).
// The `{ a?: number } = {}` declarator went silent under PITH-P037
// (absent optional member). Never silent without a reason, never forced.
const nested: { inner: { x: number } } = { inner: { x: 1 } };
const maybe: { a?: number } = {};
