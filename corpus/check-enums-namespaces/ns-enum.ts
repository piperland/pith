// Solver verdict: 1x PITH2322 (short name `Dir`) + 1x UNSUPPORTED
// (namespace-qualified value). The qualified member access `NS.Dir.Up`
// resolves silently through the P053 member-reference facts.
namespace NS { export enum Dir { Up, Down } export const VAL = 1; }
const w: NS.Dir = 0;
const bad: NS.Dir = 9;
const z: NS.Dir = NS.Dir.Up;
const y: number = NS.VAL;
