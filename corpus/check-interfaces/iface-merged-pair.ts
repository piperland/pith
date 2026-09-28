// Solver verdict: 2x UNSUPPORTED (unannotated `Foo`, non-literal init at the
// value use); tsc clean. Pins the merge path: one pre-merged symbol, and the
// interface-annotated use resolves through the same identity.
interface Foo { a: string; }
const Foo = 42;
const viaIface: Foo = { a: "s" };
const useFoo: number = Foo;
