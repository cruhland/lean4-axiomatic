
/-! # Generic definitions and properties applicable to ordered types -/

namespace Lean4Axiomatic.Ordered

/-- Provides canonical functions for minimum and maximum. -/
class Ops (α : Type u) :=
  /-- Selects the minimum of its two arguments. -/
  min : α → α → α

  /-- Selects the maximum of its two arguments. -/
  max : α → α → α

export Ops (max min)

end Lean4Axiomatic.Ordered
