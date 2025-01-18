import Lean4Axiomatic.Integer.Division

/-! # Generic implementation of integer division functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Lean4Axiomatic.Metric (abs)
open Logic (AP)

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ] [Metric ℤ]

/-- Definition of division -/
def divide (a b : ℤ) [AP (b ≄ 0)] : DivisionResult ℤ := sorry

local instance division_ops : Division.Ops ℤ := {
  divide := divide
}

/--
How the `a` in `divide a b` is split between divisor (`b`), quotient, and
remainder.
-/
theorem divide_eqv
    {a b : ℤ} [AP (b ≄ 0)] : let d := a ÷ b; a ≃ b * d.quotient + d.remainder
    := by
  admit

/-- The remainder is always nonnegative. -/
theorem remainder_lb {a b : ℤ} [AP (b ≄ 0)] : (a ÷ b).remainder ≥ 0 := by
  admit

/--
The remainder is always closer to zero than the divisor.

If this were not true, the quotient could be increased by one, and the
magnitude of the divisor subtracted from the remainder to bring it under the
limit.
-/
theorem remainder_ub {a b : ℤ} [AP (b ≄ 0)] : (a ÷ b).remainder < abs b := by
  admit

def division_props : Division.Props ℤ := {
  divide_eqv := divide_eqv
  remainder_lb := remainder_lb
  remainder_ub := remainder_ub
}

def division : Division ℤ := {
  toOps := division_ops
  toProps := division_props
}

end Lean4Axiomatic.Integer.Impl.Generic
