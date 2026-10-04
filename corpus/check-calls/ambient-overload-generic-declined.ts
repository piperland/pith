// Solver verdict: silent on the first call (the remaining checkable
// signature admits it) + 1 UNSUPPORTED on the second (the generic ambient
// signature is excluded with its own reason, so no checkable signature
// admits `true` - the oracle is clean there since it instantiates `T`).
declare function gen<T>(a: T): void;
declare function gen(a: number): void;
gen(1);
gen(true);
