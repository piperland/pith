// Fixture 3: speculative overload pick.
// Identical argument shapes resolve to different overloads by context.
function f(x: string): string;
function f(x: number): number;
function f(x: unknown): unknown { return x; }
const s: string = f("hi");
const n: number = f(42);
const u = f(true);
