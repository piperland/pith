// Solver verdict: silent, zero call facts (method calls are out of scope;
// oracle clean on the correctly-aritied method call).
const obj = {
  pick(n: number): number {
    return n;
  },
};
obj.pick(1);
