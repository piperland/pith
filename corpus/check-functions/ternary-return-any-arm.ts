// Solver verdict: one PITH2322 (the `any` parameter arm emits nothing —
// an accept-all position stays silent — while the wrong literal arm still
// diagnoses, exactly like the oracle TS2322 at that arm).
function retAnyArm(av: any, flag: boolean): number {
  return flag ? av : "oops";
}
