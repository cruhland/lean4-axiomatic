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
class Addition.Props (ℚ : Type) [Equivalence.Ops ℚ] [Ops ℚ] :=
  /-- Addition respects equivalence over its left operand. -/
  add_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ + q ≃ p₂ + q

  /-- Addition respects equivalence over its right operand. -/
  add_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q + p₁ ≃ q + p₂

export Addition.Props (add_substL add_substR)

/-- All axioms of addition for rational numbers. -/
class Addition
    (ℚ : Type) [Equivalence.Ops ℚ]
    extends Addition.Ops ℚ, Addition.Props ℚ

end Lean4Axiomatic.Rational
