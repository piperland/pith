// Solver verdict: silent (lone allowlist effect call; oracle clean —
// console.warn accepts any arguments and :void needs no return).
function warnKey(key: string): void {
  console.warn(`[destr] Dropping "${key}" key to prevent prototype pollution.`);
}
