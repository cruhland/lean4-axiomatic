import Lean4Axiomatic.Integer.Metric
import Lean4Axiomatic.Integer.Order

/-! # Integers: Euclidean division -/

namespace Lean4Axiomatic.Integer

open Lean4Axiomatic.Metric (abs)
open Logic (AP)

/-! ## Axioms -/

/-- The data returned from a Euclidean division operation. -/
structure DivisionResult (α : Type) where
  quotient : α
  remainder : α

/-- Operations for Euclidean division of integers. -/
class Division.Ops
    {ℕ : outParam Type} [Natural ℕ] (ℤ : Type) [Core (ℕ := ℕ) ℤ]
    where
  /-- Euclidean division of the first argument by the second. -/
  divide (a b : ℤ) [AP (b ≄ 0)] : DivisionResult ℤ

export Division.Ops (divide)

infix:50 " ÷ " => divide

/-- Properties of integer Euclidean division. -/
class Division.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ]
      [Negation ℤ] [Sign ℤ] [Metric ℤ] [Ops ℤ]
    where

  /--
  How the `a` in `divide a b` is split between divisor (`b`), quotient, and
  remainder.
  -/
  divide_eqv
    {a b : ℤ} [AP (b ≄ 0)] : let d := a ÷ b; a ≃ b * d.quotient + d.remainder

  /-- The remainder is always nonnegative. -/
  remainder_lb {a b : ℤ} [AP (b ≄ 0)] : (a ÷ b).remainder ≥ 0

  /--
  The remainder is always closer to zero than the divisor.

  If this were not true, the quotient could be increased by one, and the
  magnitude of the divisor subtracted from the remainder to bring it under the
  limit.
  -/
  remainder_ub {a b : ℤ} [AP (b ≄ 0)] : (a ÷ b).remainder < abs b

export Division.Props (divide_eqv remainder_lb remainder_ub)

/-- All integer Euclidean division axioms. -/
class Division
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ]
      [Negation ℤ] [Sign ℤ] [Metric ℤ]
    where
  toOps : Division.Ops ℤ
  toProps : Division.Props ℤ

attribute [instance] Division.toOps
attribute [instance] Division.toProps

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
