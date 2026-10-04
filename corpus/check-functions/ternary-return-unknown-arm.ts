// Solver verdict: one PITH2322 (the `unknown` parameter arm checks as
// `unknown` through P048 while the clean literal arm stays silent — oracle
// TS2322 at the `unknown` arm identical).
function retUnknownArm(uv: unknown, flag: boolean): string {
  return flag ? uv : "ok";
}
