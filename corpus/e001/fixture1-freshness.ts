// Fixture 1: freshness contamination.
// Same shape {a: number}; one site must FIRE excess-property check (fresh),
// the other must NOT (stale). Shared interning must not merge the verdicts.
function takesPoint(p: { x: number; y: number }) {}
const stale = { x: 1, y: 2, z: 3 };
takesPoint(stale);
takesPoint({ x: 1, y: 2, z: 3 });
