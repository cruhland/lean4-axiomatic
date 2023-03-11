import Lean4Axiomatic.Rational.Metric

/-! # Generic implementation of rational metric functions and properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Lean4Axiomatic.Metric (abs dist)
open Lean4Axiomatic.Signed (sgn)

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Sign ℚ] [Subtraction ℚ]

/-- Definition of absolute value that matches the axioms. -/
def _abs (p : ℚ) : ℚ := p * sgn p

/-- Definition of distance that matches the axioms. -/
def _dist (p q : ℚ) : ℚ := _abs (p - q)

local instance metric_ops : Metric.Ops ℚ := {
  _abs := _abs
  _dist := _dist
}

def metric_props : Metric.Props ℚ := {
  abs_sgn := eqv_refl
  dist_abs := eqv_refl
}

def metric : Metric ℚ := {
  toOps := metric_ops
  toProps := metric_props
}

end Lean4Axiomatic.Rational.Impl.Generic
