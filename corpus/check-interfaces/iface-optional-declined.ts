// Solver verdict: 2x UNSUPPORTED (optional member, one note per use); tsc clean.
interface WithOpt { a: number; b?: string; }
const absent: WithOpt = { a: 1 };
const present: WithOpt = { a: 1, b: "s" };
