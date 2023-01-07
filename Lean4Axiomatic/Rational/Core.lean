import Lean4Axiomatic.Integer

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

/-- All rational number equivalence axioms. -/
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

/--
Operations pertaining to the conversion of rational numbers into and out of
other types.
-/
class Conversion.Ops
    {ℕ : outParam Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    :=
  /-- Converts an integer into its equivalent rational number value. -/
  from_integer : ℤ → ℚ

export Conversion.Ops (from_integer)

/-- Enables the use of implicit coercions from integers to rationals. -/
instance coe_from_integer_inst
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer ℤ]
    {ℚ : Type} [Conversion.Ops (ℕ := ℕ) (ℤ := ℤ) ℚ] : Coe ℤ ℚ
    := {
  coe := from_integer
}

/-- Natural number literals can be converted into rational numbers. -/
instance of_nat_inst
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Conversion.Ops (ℤ := ℤ) ℚ] {n : Nat} : OfNat ℚ n
    := {
  ofNat := ((OfNat.ofNat n : ℤ) : ℚ)
}

/-- Properties of rational number conversion. -/
class Conversion.Props
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ] [ops : Ops (ℤ := ℤ) ℚ]
    :=
  /-- Equivalent integers are converted to equivalent rationals. -/
  from_integer_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → (a₁ : ℚ) ≃ (a₂ : ℚ)

  /-- Equivalent converted rationals came from the same integer. -/
  from_integer_inject {a₁ a₂ : ℤ} : (a₁ : ℚ) ≃ (a₂ : ℚ) → a₁ ≃ a₂

export Conversion.Props (from_integer_inject from_integer_subst)

/-- All rational number conversion axioms. -/
class Conversion
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ]
    :=
  toOps : Conversion.Ops (ℤ := ℤ) ℚ
  toProps : Conversion.Props (ℚ := ℚ) (ops := toOps)

/-- All fundamental operations on rational numbers. -/
class Core.Ops
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
    :=
  toEquivalenceOps : Equivalence.Ops ℚ
  toConversionOps : Conversion.Ops (ℤ := ℤ) ℚ

attribute [instance] Core.Ops.toEquivalenceOps
attribute [instance] Core.Ops.toConversionOps

/-- All properties of the fundamental operations on rational numbers. -/
class Core.Props
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ] [conv_ops : Conversion.Ops (ℤ := ℤ) ℚ]
    :=
  toEquivalenceProps : Equivalence.Props ℚ
  toConversionProps : Conversion.Props (ℚ := ℚ) (ops := conv_ops)

/-- All fundamental rational number axioms. -/
class Core {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ] (ℚ : Type) :=
  toOps : Core.Ops (ℤ := ℤ) ℚ
  toProps : Core.Props (ℚ := ℚ) (conv_ops := toOps.toConversionOps)

attribute [instance] Core.toOps

end Lean4Axiomatic.Rational
