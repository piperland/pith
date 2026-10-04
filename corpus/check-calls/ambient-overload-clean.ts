// Solver verdict: silent (ambient overload groups resolve by any-match -
// each call matches a different signature, and no declaration diagnostic
// fires for the missing bodies).
declare function ov(a: number): void;
declare function ov(a: string): void;
ov(1);
ov("s");
