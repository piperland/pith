// Solver verdict: 1x UNSUPPORTED (heritage clause); tsc clean.
interface Base { a: string; }
interface Child extends Base { b: number; }
const child: Child = { a: "s", b: 1 };
