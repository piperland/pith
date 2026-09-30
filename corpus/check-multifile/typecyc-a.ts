// Solver verdict: declined with reasons (re-export cycle; see README).
// Oracle tsc diagnoses TS2303 at each re-export statement (pinned gap).
export { Cyc } from "./typecyc-b";
