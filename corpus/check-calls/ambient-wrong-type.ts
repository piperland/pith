// Solver verdict: 1x PITH2345 at the mismatched argument (ambient wrong-type
// checks exactly like a lone declaration).
declare function amb(a: number): void;
amb("s");
