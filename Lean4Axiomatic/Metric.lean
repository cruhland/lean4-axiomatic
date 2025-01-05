
/-! # Functions and properties applicable to types with a metric -/

namespace Lean4Axiomatic.Metric

/--
Class for types that have a notion of distance.

Provides canonical names for the distance and absolute value functions.
-/
class MetricSpace (α : Type u) where
  /-- The [absolute value](https://w.wiki/6RCp) function. -/
  abs : α → α

  /-- The [distance, or metric](https://w.wiki/6RPu) function. -/
  dist : α → α → α

export MetricSpace (abs dist)

end Lean4Axiomatic.Metric
