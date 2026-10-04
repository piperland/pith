// Solver verdict: 1x PITH2769 with continuations on the second call (calls
// over the implementation-less group still resolve by any-match; the
// oracle's TS2391 on the declaration stays declined - the solver spells no
// declaration diagnostics).
function noimpl(a: number): void;
function noimpl(a: string): void;
noimpl(1);
noimpl(true);
