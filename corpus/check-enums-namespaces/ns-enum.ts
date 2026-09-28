// Solver verdict: 1x PITH2322 (short name `Dir`) + 2x UNSUPPORTED
// (member access, namespace-qualified value).
namespace NS { export enum Dir { Up, Down } export const VAL = 1; }
const w: NS.Dir = 0;
const bad: NS.Dir = 9;
const z: NS.Dir = NS.Dir.Up;
const y: number = NS.VAL;
