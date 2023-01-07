import Lean4Axiomatic.Rational.Addition

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
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Addition.Ops ℚ] [Ops ℚ] :=
  /-- Multiplication respects equivalence over its left operand. -/
  mul_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ * q ≃ p₂ * q

  /-- Multiplication respects equivalence over its right operand. -/
  mul_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q * p₁ ≃ q * p₂

  /-- Multiplication is consistent with its integer equivalent. -/
  mul_compat_from_integer {a b : ℤ} : ((a * b : ℤ) : ℚ) ≃ (a : ℚ) * (b : ℚ)

  /-- Multiplication is commutative. -/
  mul_comm {p q : ℚ} : p * q ≃ q * p

  /-- Multiplication is associative. -/
  mul_assoc {p q r : ℚ} : (p * q) * r ≃ p * (q * r)

  /-- One is a left multiplicative identity. -/
  mul_identL {p : ℚ} : 1 * p ≃ p

  /-- One is a right multiplicative identity. -/
  mul_identR {p : ℚ} : p * 1 ≃ p

  /-- Multiplication on the left distributes over addition. -/
  mul_distribL {p q r : ℚ} : p * (q + r) ≃ p * q + p * r

  /-- Multiplication on the right distributes over addition. -/
  mul_distribR {p q r : ℚ} : (q + r) * p ≃ q * p + r * p

export Multiplication.Props (
  mul_assoc mul_comm mul_compat_from_integer mul_distribL mul_distribR
  mul_identL mul_identR mul_substL mul_substR
)

/-- All axioms of multiplication for rational numbers. -/
class Multiplication
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Addition.Ops ℚ]
    :=
  toOps : Multiplication.Ops ℚ
  toProps : Multiplication.Props ℚ

attribute [instance] Multiplication.toOps

end Lean4Axiomatic.Rational
