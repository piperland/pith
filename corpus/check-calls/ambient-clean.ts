// Solver verdict: silent (ambient declaration checks like a lone bodied
// declaration - both calls match).
declare function amb(a: number): void;
amb(1);
amb(2);
