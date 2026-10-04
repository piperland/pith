// Solver verdict: one PITH2322 on the wrong arm (identifier arms resolve
// one level against the parameter, then check like literals — oracle
// TS2322 on the parameter arm only; the clean declaration stays silent).
function retIdentWrong(xParam: number, flag: boolean): string {
  return flag ? xParam : "ok";
}
function retIdentClean(xParam: number, flag: boolean): number {
  return flag ? xParam : 1;
}
