import Lean4Axiomatic.Operators
import Lean4Axiomatic.Relation.Equivalence

/-! # Rational numbers: fundamental definitions and properties -/

namespace Lean4Axiomatic.Rational

/-- Operations pertaining to rational number equivalence. -/
class Equivalence.Ops (ℚ : Type) :=
  /-- Equivalence relation; holds if the inputs have the same numeric value. -/
  eqv : ℚ → ℚ → Prop

export Equivalence.Ops (eqv)

/-- Enables the use of the `· ≃ ·` operator for equivalence. -/
instance eqv_tilde_dash_inst
    {ℚ : Type} [Equivalence.Ops ℚ] : Operators.TildeDash ℚ
    := {
  tildeDash := eqv
}

/-- Properties of rational number equivalence. -/
class Equivalence.Props (ℚ : Type) [Ops ℚ] :=
  /-- Equivalence is reflexive. -/
  eqv_refl {p : ℚ} : p ≃ p

  /-- Equivalence is symmetric. -/
  eqv_symm {p q : ℚ} : p ≃ q → q ≃ p

  /-- Equivalence is transitive. -/
  eqv_trans {p q r : ℚ} : p ≃ q → q ≃ r → p ≃ r

export Equivalence.Props (eqv_refl eqv_symm eqv_trans)

/-- All axioms of equivalence for rational numbers. -/
class Equivalence (ℚ : Type) extends Equivalence.Ops ℚ, Equivalence.Props ℚ

/--
Rational number equivalence is an equivalence relation.

This enables it to be used in generic contexts; for example, as a relation in
`calc` expressions.
-/
instance eqv_op_inst
    {ℚ : Type} [Equivalence ℚ] : Relation.Equivalence.EqvOp ℚ
    := {
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans
}

end Lean4Axiomatic.Rational
