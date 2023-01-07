import Lean4Axiomatic.Logic
import Lean4Axiomatic.Rational.Core

/-! # Rational numbers: inverse operations -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

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

/-- All rational number negation axioms. -/
class Negation
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  toOps : Negation.Ops ℚ
  toProps : Negation.Props (ℚ := ℚ) (core_ops := core_ops)

/-- Operations pertaining to rational number reciprocation. -/
class Reciprocation.Ops
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  /-- Reciprocation of rational numbers. -/
  reciprocal (p : ℚ) [AP (p ≄ 0)] : ℚ

export Reciprocation.Ops (reciprocal)

postfix:120 "⁻¹" => reciprocal

/-- All rational number reciprocation axioms. -/
class Reciprocation
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  toOps : Reciprocation.Ops (ℚ := ℚ) (core_ops := core_ops)

/-- All rational number inverse operation axioms. -/
class Inverse
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  toNegation : Negation (ℚ := ℚ) (core_ops := core_ops)
  toReciprocation : Reciprocation (ℚ := ℚ) (core_ops := core_ops)

end Lean4Axiomatic.Rational
