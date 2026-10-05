// Solver verdict: silent (`any` receivers absorb every method).
const av: any = 1;
const a: string = av.trim();
const b: string = av.split(",");
const c: string[] = av.split(",");
const d: number = av.slice(0);
