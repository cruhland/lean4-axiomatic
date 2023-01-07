import Lean4Axiomatic.Logic
import Lean4Axiomatic.Rational.Multiplication

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
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Addition.Ops ℚ] [Ops ℚ]
    :=
  /-- Negation respects equivalence over its operand. -/
  neg_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → -p₁ ≃ -p₂

  /-- Negation is consistent with its integer equivalent. -/
  neg_compat_from_integer {a : ℤ} : ((-a : ℤ) : ℚ) ≃ -(a : ℚ)

  /-- The negation of a value is its left additive inverse. -/
  add_inverseL {p : ℚ} : -p + p ≃ 0

  /-- The negation of a value is its right additive inverse. -/
  add_inverseR {p : ℚ} : p + -p ≃ 0

export Negation.Props (
  add_inverseL add_inverseR neg_compat_from_integer neg_subst
)

/-- All rational number negation axioms. -/
class Negation
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Addition.Ops ℚ]
    :=
  toOps : Negation.Ops ℚ
  toProps : Negation.Props ℚ

/-- Operations pertaining to rational number reciprocation. -/
class Reciprocation.Ops
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ]
    :=
  /-- Reciprocation of rational numbers. -/
  reciprocal (p : ℚ) [AP (p ≄ 0)] : ℚ

export Reciprocation.Ops (reciprocal)

postfix:120 "⁻¹" => reciprocal

class Reciprocation.Props
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Multiplication.Ops ℚ] [Ops ℚ]
    :=
  /-- Reciprocation respects equivalence over its operand. -/
  recip_subst {p₁ p₂ : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹

  /-- The reciprocal of a value is its left multiplicative inverse. -/
  recip_inverseL {p : ℚ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1

  /-- The reciprocal of a value is its right multiplicative inverse. -/
  recip_inverseR {p : ℚ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1

export Reciprocation.Props (recip_inverseL recip_inverseR recip_subst)

/-- All rational number reciprocation axioms. -/
class Reciprocation
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Multiplication.Ops ℚ]
    :=
  toOps : Reciprocation.Ops ℚ
  toProps : Reciprocation.Props ℚ

/-- All rational number inverse operation axioms. -/
class Inverse
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Addition.Ops ℚ] [Multiplication.Ops ℚ]
    :=
  toNegation : Negation ℚ
  toReciprocation : Reciprocation ℚ

end Lean4Axiomatic.Rational
