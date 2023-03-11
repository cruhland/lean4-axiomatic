import Lean4Axiomatic.Metric
import Lean4Axiomatic.Rational.Sign

/-! # Rational numbers: metric functions -/

namespace Lean4Axiomatic.Rational

open Metric (abs dist MetricSpace)
open Signed (sgn)

/-! ## Axioms -/

/-- Operations pertaining to metrics on rational numbers. -/
class Metric.Ops (ℚ : Type) :=
  /-- Absolute value. -/
  _abs : ℚ → ℚ

  /-- Distance. -/
  _dist : ℚ → ℚ → ℚ

/-- Enables the use of the standard names for absolute value and distance. -/
instance metric_space_inst {ℚ : Type} [Metric.Ops ℚ] : MetricSpace ℚ := {
  abs := Metric.Ops._abs
  dist := Metric.Ops._dist
}

/-- Properties of rational number metrics. -/
class Metric.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Ops ℚ]
    :=
  /--
  The absolute value of a rational number is equivalent to the product of that
  number with its sign.
  -/
  abs_sgn {p : ℚ} : abs p ≃ p * sgn p

  /--
  The distance between two rational numbers is the absolute value of their
  difference.
   -/
  dist_abs {p q : ℚ} : dist p q ≃ abs (p - q)

export Metric.Props (abs_sgn dist_abs)

/-- All rational number metric axioms. -/
class Metric
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ]
    :=
  toOps : Metric.Ops ℚ
  toProps : Metric.Props ℚ

attribute [instance] Metric.toOps
attribute [instance] Metric.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Metric ℚ]

/--
The absolute value function preserves equivalence over its argument.

**Property intuition**: This must be the case for `abs` to be a function.

**Proof intuition**: Expand `abs` into its `sgn` definition, and use
substitution on multiplication and `sgn`.
-/
theorem abs_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → abs p₁ ≃ abs p₂ := by
  intro (_ : p₁ ≃ p₂)
  show abs p₁ ≃ abs p₂
  calc
    abs p₁      ≃ _ := abs_sgn
    p₁ * sgn p₁ ≃ _ := mul_substL ‹p₁ ≃ p₂›
    p₂ * sgn p₁ ≃ _ := mul_substR (from_integer_subst (sgn_subst ‹p₁ ≃ p₂›))
    p₂ * sgn p₂ ≃ _ := eqv_symm abs_sgn
    abs p₂      ≃ _ := eqv_refl

end Lean4Axiomatic.Rational
