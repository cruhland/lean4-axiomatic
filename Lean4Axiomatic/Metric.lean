
/-! # Functions and properties applicable to types with a metric -/

namespace Lean4Axiomatic.Metric

/--
Class for types that have a notion of absolute value.

Provides a canonical name for the absolute value function, `abs`.
-/
class AbsoluteValue (α : Type u) :=
  /-- The [absolute value](https://w.wiki/6RCp) function. -/
  abs : α → α

export AbsoluteValue (abs)

end Lean4Axiomatic.Metric
