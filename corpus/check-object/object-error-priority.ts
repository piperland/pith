// Solver verdict: one PITH2322 (wrong beats excess) plus one PITH2353
// (excess beats missing). tsc reports exactly one family per declaration.
const wrongBeatsExcess: { x: number } = { x: "s", extra: 1 };
const excessBeatsMissing: { x: number; y: string } = { x: 1, extra: 2 };
