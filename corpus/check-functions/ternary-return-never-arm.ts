// Solver verdict: one PITH2322 (a `never` arm vanishes from the union
// while the other arm still checks — oracle TS2322 at the wrong literal
// arm only; the clean declaration stays silent).
function retNeverWrong(nvr: never, flag: boolean): number {
  return flag ? nvr : "oops";
}
function retNeverClean(nvr: never, flag: boolean): number {
  return flag ? nvr : 1;
}
