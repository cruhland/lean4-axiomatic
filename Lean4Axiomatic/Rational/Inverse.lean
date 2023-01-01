
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

/-- All axioms of negation for rational numbers. -/
class Negation (ℚ : Type) extends Negation.Ops ℚ

end Lean4Axiomatic.Rational
