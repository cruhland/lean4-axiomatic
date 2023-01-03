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
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ] [Ops ℚ]
    :=
  /-- Addition respects equivalence over its left operand. -/
  add_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ + q ≃ p₂ + q

  /-- Addition respects equivalence over its right operand. -/
  add_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q + p₁ ≃ q + p₂

  /-- Addition is consistent with its integer equivalent. -/
  add_compat_from_integer {a b : ℤ} : ((a + b : ℤ) : ℚ) ≃ (a : ℚ) + (b : ℚ)

export Addition.Props (add_compat_from_integer add_substL add_substR)

/-- All axioms of addition for rational numbers. -/
class Addition
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [core_ops : Core.Ops (ℤ := ℤ) ℚ]
    :=
  toOps : Addition.Ops ℚ
  toProps : Addition.Props (ℚ := ℚ) (core_ops := core_ops)

end Lean4Axiomatic.Rational
