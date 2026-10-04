function pick(a: number): number;
function pick(a: string): string;
function pick(a: any): any {
  return 1;
}
pick(1);
pick("s");
