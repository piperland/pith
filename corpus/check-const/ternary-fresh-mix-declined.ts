// Solver verdict: UNSUPPORTED (a literal arm beside an identifier arm of
// another kind would need the oracle's fresh spelling `number | "ok"`,
// which widened-only spellings refuse to fake — oracle TS2322, a pinned
// oracle-error divergence under the P034 no-misspelling discipline).
const xFresh: number = 1;
const flag: boolean = true;
const tFresh: string = flag ? xFresh : "ok";
