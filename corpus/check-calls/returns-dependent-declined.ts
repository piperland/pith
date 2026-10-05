function idem<T>(f: (x: T) => T): T {
  throw new Error("x");
}
idem((x) => "hi");
