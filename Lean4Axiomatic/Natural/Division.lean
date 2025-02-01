import Lean4Axiomatic.Natural.Multiplication

/-! # Natural numbers: Euclidean division -/

namespace Lean4Axiomatic.Natural

open Logic (AP)

/-! ## Axioms -/

/--
Demonstrates a valid [Euclidean division](https://w.wiki/CnLb) of the first
parameter by the second.
-/
structure EuclideanDivision
    {ℕ : Type} [Core ℕ] [Addition ℕ] [Order ℕ] [Multiplication ℕ] (n m : ℕ)
    where
  /--
  The [quotient](https://w.wiki/CnLh) is the number of `m`s that can be added
  together without exceeding `n`.
  -/
  quotient : ℕ

  /--
  The [remainder](https://w.wiki/CnLt) is the amount to add to `m * quotient`
  to reach `n`.
  -/
  remainder : ℕ

  /-- How `n` is split between divisor (`m`), quotient, and remainder. -/
  div_eqv : n ≃ m * quotient + remainder

  /--
  The remainder is smaller than the divisor (`m`).

  If this were not true, the quotient could be increased by one, and the
  divisor subtracted from the remainder to bring it under the limit.
  -/
  rem_ub : remainder < m

/-- All natural number Euclidean division axioms. -/
class Division
    (ℕ : Type) [Core ℕ] [Addition ℕ] [Order ℕ] [Multiplication ℕ]
    where
  /-- Computes the Euclidean division of the first argument by the second. -/
  divide (n m : ℕ) [AP (m ≄ 0)] : EuclideanDivision n m

export Division (divide)

/-! ## Derived properties -/

variable
  {ℕ : Type} [Core ℕ] [Addition ℕ] [Order ℕ] [Multiplication ℕ] [Division ℕ]

/-- Enables the `· ÷ ·` operator to be used for natural number division. -/
instance divide_op_inst
    : Operators.DivisionSign (λ n m : ℕ => [AP (m ≄ 0)] → EuclideanDivision n m)
    := {
  divisionSign := divide
}

end Lean4Axiomatic.Natural
