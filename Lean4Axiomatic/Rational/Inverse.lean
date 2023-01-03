import Lean4Axiomatic.Rational.Core

/-! # Rational numbers: inverse operations -/

namespace Lean4Axiomatic.Rational

/-- Operations pertaining to rational number negation. -/
class Negation.Ops (ℚ : Type) :=
  /-- Negation of rational numbers. -/
  neg : ℚ → ℚ

export Negation.Ops (neg)

/-- Enables the use of the `-·` operator for negation. -/
instance neg_op_inst {ℚ : Type} [Negation.Ops ℚ] : Neg ℚ := {
  neg := neg
}

/-- Properties of rational number negation. -/
class Negation.Props
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ] [Ops ℚ] :=
  /-- Negation respects equivalence over its operand. -/
  neg_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → -p₁ ≃ -p₂

  /-- Negation is consistent with its integer equivalent. -/
  neg_compat_from_integer {a : ℤ} : ((-a : ℤ) : ℚ) ≃ -(a : ℚ)

export Negation.Props (neg_compat_from_integer neg_subst)

/-- All axioms of negation for rational numbers. -/
class Negation
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  toOps : Negation.Ops ℚ
  toProps : Negation.Props (ℚ := ℚ) (core_ops := core_ops)

end Lean4Axiomatic.Rational
