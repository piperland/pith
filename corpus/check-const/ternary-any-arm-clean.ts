// Solver verdict: silent (`any` absorbs the union, so the whole ternary
// stays silent — oracle clean).
const av: any = 1;
const flag: boolean = true;
const tAny: number = flag ? av : 2;
