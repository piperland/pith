// Solver verdict: UNSUPPORTED (non-literal returns and cast operands carry
// no value-type facts; oracle clean — pinned divergence). Destr-shaped:
// `any` parameters plus an `unknown`-bound return with an `as` assertion.
function jsonParseTransform(key: string, value: any): any {
  return value;
}
function destr(value: any): unknown {
  return value as unknown;
}
