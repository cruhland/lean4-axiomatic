import Lean4Axiomatic.Integer.Metric
import Lean4Axiomatic.Integer.Order

/-! # Integers: Euclidean division -/

namespace Lean4Axiomatic.Integer

open Lean4Axiomatic.Metric (abs)
open Logic (AP)

/-! ## Axioms -/

/--
Demonstrates a valid [Euclidean division](https://w.wiki/CnLb) of the first
parameter by the second.
-/
structure EuclideanDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ]
    (a b : ℤ)
    where
  /--
  The [quotient](https://w.wiki/CnLh) is the number of `b`s that can be added
  together without exceeding `a`.
  -/
  quotient : ℤ

  /--
  The [remainder](https://w.wiki/CnLt) is the amount to add to `b * quotient`
  to reach `a`.
  -/
  remainder : ℤ

  /-- How `a` is split between divisor (`b`), quotient, and remainder. -/
  div_eqv : a ≃ b * quotient + remainder

  /-- The remainder is nonnegative. -/
  rem_lb : remainder ≥ 0

  /--
  The remainder is closer to zero than the divisor (`b`).

  If this were not true, the quotient could be increased or decreased by one,
  and the magnitude of the divisor subtracted from the remainder to bring it
  under the limit.
  -/
  rem_ub : remainder < abs b

/-- All integer Euclidean division axioms. -/
class Division
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ]
    where
  /-- Computes the Euclidean division of the first argument by the second. -/
  divide (a b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b

export Division (divide)

infix:50 " ÷ " => divide

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ] [Metric ℤ] [Division ℤ]

/--
Sufficient condition for the quotients of two integer divisions to be
equivalent.
-/
theorem quotient_eqv
    {a₁ a₂ b₁ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
    : a₁ * b₂ ≃ a₂ * b₁ → (a₁ ÷ b₁).quotient ≃ (a₂ ÷ b₂).quotient
    := by
  admit

end Lean4Axiomatic.Integer
