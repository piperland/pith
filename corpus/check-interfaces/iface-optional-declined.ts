// Solver verdict: silent (optional members: absent silent, present checks).
// Formerly 2x UNSUPPORTED (optional member, one note per use); tsc clean.
// Converted by PITH-P037: the range/member flip.
interface WithOpt { a: number; b?: string; }
const absent: WithOpt = { a: 1 };
const present: WithOpt = { a: 1, b: "s" };
