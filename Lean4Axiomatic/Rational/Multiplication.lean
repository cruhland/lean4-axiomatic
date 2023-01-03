import Lean4Axiomatic.Rational.Core

/-! # Rational numbers: multiplication -/

namespace Lean4Axiomatic.Rational

/-- Operations pertaining to rational number multiplication. -/
class Multiplication.Ops (ℚ : Type) :=
  /-- Multiplication of rational numbers. -/
  mul : ℚ → ℚ → ℚ

export Multiplication.Ops (mul)

/-- Enables the use of the `· * ·` operator for multiplication. -/
instance mul_op_inst {ℚ : Type} [Multiplication.Ops ℚ] : Mul ℚ := {
  mul := mul
}

/-- Properties of rational number multiplication. -/
class Multiplication.Props
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ] [Ops ℚ] :=
  /-- Multiplication respects equivalence over its left operand. -/
  mul_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ * q ≃ p₂ * q

  /-- Multiplication respects equivalence over its right operand. -/
  mul_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q * p₁ ≃ q * p₂

  /-- Multiplication is consistent with its integer equivalent. -/
  mul_compat_from_integer {a b : ℤ} : ((a * b : ℤ) : ℚ) ≃ (a : ℚ) * (b : ℚ)

export Multiplication.Props (mul_compat_from_integer mul_substL mul_substR)

/-- All axioms of multiplication for rational numbers. -/
class Multiplication
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  toOps : Multiplication.Ops ℚ
  toProps : Multiplication.Props (ℚ := ℚ) (core_ops := core_ops)

end Lean4Axiomatic.Rational
