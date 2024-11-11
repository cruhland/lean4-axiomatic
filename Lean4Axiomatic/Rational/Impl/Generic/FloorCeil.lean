import Lean4Axiomatic.Rational.FloorCeil

/-! # Generic implementation of rational floor and ceiling, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ]

def floor (p : ℚ) : ℤ := sorry

def ceil (p : ℚ) : ℤ := sorry

local instance floor_ceil_ops : FloorCeil.Ops ℤ ℚ := {
  floor := floor
  ceil := ceil
}

theorem floor_ub {p : ℚ} : (floor p : ℤ) ≤ p := sorry

theorem floor_lb {p : ℚ} {a : ℤ} : a ≤ p → a ≤ floor p := sorry

theorem ceil_lb {p : ℚ} : p ≤ (ceil p : ℤ) := sorry

theorem ceil_ub {p : ℚ} {a : ℤ} : p ≤ a → ceil p ≤ a := sorry

def floor_ceil_props : FloorCeil.Props ℚ := {
  floor_ub := floor_ub
  floor_lb := floor_lb
  ceil_lb := ceil_lb
  ceil_ub := ceil_ub
}

def floor_ceil : FloorCeil ℚ := {
  toOps := floor_ceil_ops
  toProps := floor_ceil_props
}

end Lean4Axiomatic.Rational.Impl.Generic
