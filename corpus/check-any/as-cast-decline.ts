// Solver verdicts: one PITH2352 per declined cast plus the downstream
// check (oracle TS2352 + TS2322/TS2345); the angle assertion shares the
// `as` rule.
const s: string = ("hello" as number);
const t: number = (<string>1);
function sn(x: string): number {
  return 1;
}
sn(("hello" as number));
