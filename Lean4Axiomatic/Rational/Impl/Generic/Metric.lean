import Lean4Axiomatic.Rational.Metric

/-! # Generic implementation of rational metric functions and properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Signed (sgn)

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]

/-- Definition of absolute value that matches the axioms. -/
def _abs (p : ℚ) : ℚ := p * sgn p

local instance metric_ops : Metric.Ops ℚ := {
  _abs := _abs
}

def metric_props : Metric.Props ℚ := {
  abs_sgn := eqv_refl
}

def metric : Metric ℚ := {
  toOps := metric_ops
  toProps := metric_props
}

end Lean4Axiomatic.Rational.Impl.Generic
