// Solver verdict: four UNSUPPORTED (known members with uncheckable lib
// shapes: range arity, overloads, variadics. Oracle clean pins the
// divergence). Mirrors the destr `JSON.parse(value)` / `console.warn(...)`
// sites, which land on the same lib reasons.
declare const v: any;
JSON.parse(v);
console.warn("x");
JSON.stringify(v);
Math.max(1, 2);
