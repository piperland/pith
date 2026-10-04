// Solver verdict: 2x UNSUPPORTED, one per signature (ambient overload
// groups carry no bodies to check - the oracle is clean, so this pins the
// divergence; never a declaration diagnostic for the missing bodies).
declare function ov(a: number): void;
declare function ov(a: string): void;
