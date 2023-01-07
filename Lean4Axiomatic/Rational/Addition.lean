import Lean4Axiomatic.Rational.Core

/-! # Rational numbers: addition -/

namespace Lean4Axiomatic.Rational

/-- Operations pertaining to rational number addition. -/
class Addition.Ops (ℚ : Type) :=
  /-- Addition of rational numbers. -/
  add : ℚ → ℚ → ℚ

export Addition.Ops (add)

/-- Enables the use of the `· + ·` operator for addition. -/
instance add_op_inst {ℚ : Type} [Addition.Ops ℚ] : Add ℚ := {
  add := add
}

/-- Properties of rational number addition. -/
class Addition.Props
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ] [Ops ℚ]
    :=
  /-- Addition respects equivalence over its left operand. -/
  add_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ + q ≃ p₂ + q

  /-- Addition respects equivalence over its right operand. -/
  add_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q + p₁ ≃ q + p₂

  /-- Addition is consistent with its integer equivalent. -/
  add_compat_from_integer {a b : ℤ} : ((a + b : ℤ) : ℚ) ≃ (a : ℚ) + (b : ℚ)

  /-- Addition is commutative. -/
  add_comm {p q : ℚ} : p + q ≃ q + p

  /-- Addition is associative. -/
  add_assoc {p q r : ℚ} : (p + q) + r ≃ p + (q + r)

  /-- Zero is a left additive identity. -/
  add_identL {p : ℚ} : 0 + p ≃ p

  /-- Zero is a right additive identity. -/
  add_identR {p : ℚ} : p + 0 ≃ p

export Addition.Props (
  add_assoc add_comm add_compat_from_integer add_identL add_identR add_substL
  add_substR
)

/-- All axioms of addition for rational numbers. -/
class Addition
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core.Ops (ℤ := ℤ) ℚ]
    :=
  toOps : Addition.Ops ℚ
  toProps : Addition.Props ℚ

attribute [instance] Addition.toOps

end Lean4Axiomatic.Rational
