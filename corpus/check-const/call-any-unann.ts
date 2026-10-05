// Solver verdict: silent (unannotated `any`-results absorb via P025).
const a = JSON.parse('"hi"');
const b = Object.getPrototypeOf({});
const av: any = 1;
const c = av.trim();
