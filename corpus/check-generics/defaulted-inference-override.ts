// Solver verdict: silent default-filled call + 1x PITH2345 (explicit `string` override against `number`) + 2 UNSUPPORTED (body `return x`, ambient-sourced ident arg `u`).
function idd<T = number>(x: T): T {
  return x;
}
declare const u: number;
const a = idd(u);
const b = idd<string>(1);
