import Lean4Axiomatic.Integer.Metric
import Lean4Axiomatic.Integer.Order

/-! # Integers: Division -/

namespace Lean4Axiomatic.Integer

open Lean4Axiomatic.Metric (abs)
open Logic (AP)
open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

/--
Any division operation of the first parameter by the second must satisfy these
requirements.
-/
structure BaseDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Metric ℤ] [Order ℤ]
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

  /--
  The remainder is closer to zero than the divisor (`b`).

  If this were not true, the quotient could be increased or decreased by one,
  and the magnitude of the divisor subtracted from the remainder to bring it
  under the limit.
  -/
  rem_mag : abs remainder < abs b

/--
Demonstrates a valid [Euclidean division](https://w.wiki/CnLb) of the first
parameter by the second.
-/
structure EuclideanDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Metric ℤ] [Order ℤ]
    (a b : ℤ) extends BaseDivision a b
    where
  /-- The remainder is nonnegative. -/
  rem_sgn : remainder ≥ 0

/--
Demonstrates a valid [floored division](https://w.wiki/Cyft) of the first
parameter by the second.
-/
structure FlooredDivision
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Metric ℤ] [Order ℤ]
    (a b : ℤ) extends BaseDivision a b
    where
  /-- The remainder is either zero or the same sign as the divisor. -/
  rem_sgn : remainder * b ≥ 0

/-- All integer division axioms. -/
class Division
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ]
    where
  /-- Computes the Euclidean division of the first argument by the second. -/
  div_euclidean (a b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b

  /-- Computes the floored division of the first argument by the second. -/
  div_floored (a b : ℤ) [AP (b ≄ 0)] : FlooredDivision a b

export Division (div_euclidean div_floored)

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ] [Metric ℤ] [Division ℤ]

def BaseDivision.to_prod
    {a b : ℤ} (d : BaseDivision a b) : ℤ × ℤ
    :=
  sorry

instance base_div_eqv_op_inst {a b : ℤ} : EqvOp (BaseDivision a b) := sorry

theorem base_div_unique {a b : ℤ} {d₁ d₂ : BaseDivision a b} : d₁ ≃ d₂ := by
  admit

theorem div_floored_substL_quot
    {a₁ a₂ b : ℤ} {d₁ : FlooredDivision a₁ b} {d₂ : FlooredDivision a₂ b}
    : a₁ ≃ a₂ → d₁.quotient ≃ d₂.quotient
    := by
  admit

theorem div_floored_substR_quot
    {a₁ a₂ b : ℤ} {d₁ : FlooredDivision b a₁} {d₂ : FlooredDivision b a₂}
    : a₁ ≃ a₂ → d₁.quotient ≃ d₂.quotient
    := by
  admit

theorem div_floored_mulR_eqv
    {a b c : ℤ}
    {d : FlooredDivision a b} {dc : FlooredDivision (a * c) (b * c)}
    : dc.quotient ≃ d.quotient
    := by
  /-
  (div_floored a b).q ≃ (div_floored (a * c) (b * c)).q, c ≄ 0
  a ≃ b * q + r
  from divsion: a * c ≃ (b * c) * q_c + r_c
  from multiplying:
      a * c
    ≃ (b * q + r) * c
    ≃ (b * q) * c + r * c
    ≃ (b * c) * q + r * c
  by uniqueness, q ≃ q_c
  -/
  admit

/--
Sufficient condition for the quotients of two integer floored divisions to be
equivalent.
-/
theorem div_floored_quotient_eqv
    {a₁ a₂ b₁ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
    : a₁ * b₂ ≃ a₂ * b₁ →
      (div_floored a₁ b₁).quotient ≃ (div_floored a₂ b₂).quotient
    := by
  intro (_ : a₁ * b₂ ≃ a₂ * b₁)
  show (div_floored a₁ b₁).quotient ≃ (div_floored a₂ b₂).quotient

  -- Instances needed for divisors in division operations below
  have : b₁ ≄ 0 ∧ b₂ ≄ 0 := And.intro ‹AP (b₁ ≄ 0)›.ev ‹AP (b₂ ≄ 0)›.ev
  have : AP (b₁ * b₂ ≄ 0) := AP.mk (mul_split_neqv_zero.mpr ‹b₁ ≄ 0 ∧ b₂ ≄ 0›)
  have : AP (b₂ * b₁ ≄ 0) := ‹AP (b₁ * b₂ ≄ 0)›.map (AA.neqv_substL AA.comm)

  -- Abbreviate quotient expression to keep the calc block inside margin
  let dfq (x y : ℤ) [AP (y ≄ 0)] : ℤ := (div_floored x y).quotient
  show dfq a₁ b₁ ≃ dfq a₂ b₂
  calc
    _ = dfq a₁ b₁               := rfl
    _ ≃ dfq (a₁ * b₂) (b₁ * b₂) := Rel.symm div_floored_mulR_eqv
    _ ≃ dfq (a₂ * b₁) (b₁ * b₂) := div_floored_substL_quot ‹a₁ * b₂ ≃ a₂ * b₁›
    _ ≃ dfq (a₂ * b₁) (b₂ * b₁) := div_floored_substR_quot AA.comm
    _ ≃ dfq a₂ b₂               := div_floored_mulR_eqv

end Lean4Axiomatic.Integer
