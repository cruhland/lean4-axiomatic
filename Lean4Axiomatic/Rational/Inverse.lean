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
class Negation.Props (ℚ : Type) [Equivalence.Ops ℚ] [Ops ℚ] :=
  /-- Negation respects equivalence over its operand. -/
  neg_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → -p₁ ≃ -p₂

export Negation.Props (neg_subst)

/-- All axioms of negation for rational numbers. -/
class Negation
    (ℚ : Type) [Equivalence.Ops ℚ]
    extends Negation.Ops ℚ, Negation.Props ℚ

end Lean4Axiomatic.Rational
