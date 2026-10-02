// Solver verdict: clean oracle + 1 UNSUPPORTED (named-shape aliases check
// through the interface/enum entry points; check_file holds no shape tables).
interface Point {
  x: number;
  y: number;
}
type Alias = Point;
const a: Alias = { x: 1, y: 2 };
