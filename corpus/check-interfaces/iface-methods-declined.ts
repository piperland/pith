// Solver verdict: 2x UNSUPPORTED (method member, index member); tsc clean.
interface Runner { run(n: number): string; }
const runner: Runner = { run: (n: number) => "go" };
interface Table { [key: string]: number; }
const lookup: Table = { a: 1 };
