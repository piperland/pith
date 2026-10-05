// Solver verdict: silent (`any` absorbs every annotation).
const a: string = JSON.parse('"hi"');
const b: number = JSON.parse('"hi"');
const c: boolean = Object.getPrototypeOf({});
const d: any = JSON.parse('"hi"');
