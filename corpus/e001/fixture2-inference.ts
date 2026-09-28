// Fixture 2: provisional generic inference.
// Identical argument shapes; contextual return-position typing must yield
// different T per call site under a shared interner.
function id<T>(x: T): T { return x; }
const a: string = id({ v: 1 });
const b: number = id({ v: 1 });
