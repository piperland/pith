// Solver verdict: one PITH2322 (the condition never narrows — a call
// condition qualifies exactly like a plain one, and no condition facts
// flow — so this matches the wrong-then message exactly).
const tCond: number = Math.random() > 0.5 ? 1 : "oops";
