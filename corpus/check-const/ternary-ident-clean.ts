// Solver verdict: silent (identifier arms resolve one level through the
// P048 table, then check like literals — oracle clean on both).
const xIdent: number = 1;
const yIdent: number = 2;
const flag: boolean = true;
const tIdentA: number = flag ? xIdent : 2;
const tIdentB: number = flag ? xIdent : yIdent;
