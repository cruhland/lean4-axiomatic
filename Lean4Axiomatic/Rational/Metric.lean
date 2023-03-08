import Lean4Axiomatic.Metric
import Lean4Axiomatic.Rational.Sign

/-! # Rational numbers: metric functions -/

namespace Lean4Axiomatic.Rational

open Metric (abs AbsoluteValue)
open Signed (sgn)

/-! ## Axioms -/

/-- Operations pertaining to metrics on rational numbers. -/
class Metric.Ops (ℚ : Type) :=
  /-- Absolute value. -/
  _abs : ℚ → ℚ

/-- Enables the use of the standard `abs` name for absolute value. -/
instance abs_inst {ℚ : Type} [Metric.Ops ℚ] : AbsoluteValue ℚ := {
  abs := Metric.Ops._abs
}

/-- Properties of rational number metrics. -/
class Metric.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Ops ℚ]
    :=
  /--
  The absolute value of a rational number is equivalent to the product of that
  number with its sign.
  -/
  abs_sgn {p : ℚ} : abs p ≃ p * sgn p

export Metric.Props (abs_sgn)

/-- All rational number metric axioms. -/
class Metric
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]
    :=
  toOps : Metric.Ops ℚ
  toProps : Metric.Props ℚ

attribute [instance] Metric.toOps
attribute [instance] Metric.toProps

end Lean4Axiomatic.Rational
