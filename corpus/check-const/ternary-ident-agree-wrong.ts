// Solver verdict: one PITH2322 (the identifier arm resolves to `number`,
// agreeing with the literal arm, so the declaration checks as one literal
// through the existing path — oracle TS2322 spelling `number`).
const xAgree: number = 1;
const flag: boolean = true;
const tAgree: string = flag ? xAgree : 2;
