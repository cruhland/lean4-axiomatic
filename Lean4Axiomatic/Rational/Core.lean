import Lean4Axiomatic.Integer

/-! # Rational numbers: fundamental definitions and properties -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

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
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    :=
  /-- Converts an integer into its equivalent rational number value. -/
  from_integer : ℤ → ℚ

export Conversion.Ops (from_integer)

/-- Enables the use of implicit coercions from integers to rationals. -/
instance coe_from_integer_inst
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Conversion.Ops (ℤ := ℤ) ℚ] : Coe ℤ ℚ
    := {
  coe := from_integer
}

/-- Natural number literals can be converted into rational numbers. -/
instance of_nat_inst
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Conversion.Ops (ℤ := ℤ) ℚ] {n : Nat} : OfNat ℚ n
    := {
  ofNat := ((OfNat.ofNat n : ℤ) : ℚ)
}

/-- Properties of rational number conversion. -/
class Conversion.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ] [Ops (ℤ := ℤ) ℚ]
    :=
  /-- Equivalent integers are converted to equivalent rationals. -/
  from_integer_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → (a₁ : ℚ) ≃ (a₂ : ℚ)

  /-- Equivalent converted rationals came from the same integer. -/
  from_integer_inject {a₁ a₂ : ℤ} : (a₁ : ℚ) ≃ (a₂ : ℚ) → a₁ ≃ a₂

export Conversion.Props (from_integer_inject from_integer_subst)

/-- All rational number conversion axioms. -/
class Conversion
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Equivalence.Ops ℚ]
    :=
  toOps : Conversion.Ops (ℤ := ℤ) ℚ
  toProps : Conversion.Props ℚ

attribute [instance] Conversion.toOps
attribute [instance] Conversion.toProps

/-- All fundamental rational number axioms. -/
class Core {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] (ℚ : Type) :=
  toEquivalence : Equivalence ℚ
  toConversion : Conversion (ℤ := ℤ) ℚ

attribute [instance] Core.toConversion
attribute [instance] Core.toEquivalence

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type} [Core (ℤ := ℤ) ℚ]

/--
If `Integer.Nonzero` holds for an integer, then `· ≄ 0` holds for its rational
equivalent.

**Property intuition**: Since the integers are embedded in the rationals, we
expect that integer properties hold for their embedded versions.

**Proof intuition**: We assume `(a : ℚ) ≃ 0` because we are trying to show its
negation. This implies that `a ≃ 0` (as an integer), but this contradicts the
`Integer.Nonzero` assumption.
-/
theorem from_integer_preserves_nonzero
    {a : ℤ} : Integer.Nonzero a → (a : ℚ) ≄ 0
    := by
  intro (_ : Integer.Nonzero a) (_ : (a : ℚ) ≃ 0)
  show False
  have : a ≄ 0 := Integer.nonzero_iff_neqv_zero.mp ‹Integer.Nonzero a›
  have : (a : ℚ) ≃ (0 : ℚ) := ‹(a : ℚ) ≃ 0›
  have : a ≃ 0 := from_integer_inject this
  exact absurd ‹a ≃ 0› ‹a ≄ 0›

/-- Make `from_integer_preserves_nonzero` available for instance search. -/
instance from_integer_preserves_nonzero_inst
    {a : ℤ} [Integer.Nonzero a] : AP ((a : ℚ) ≄ 0)
    :=
  AP.mk (from_integer_preserves_nonzero ‹Integer.Nonzero a›)

/--
One and zero are distinct rational numbers.

**Intuition**: They are also distinct integers, and their rational number
equivalents obey the same properties.
-/
theorem nonzero_one : (1 : ℚ) ≄ 0 := from_integer_preserves_nonzero_inst.ev

/--
For some reason Lean's instance search won't derive this from
`from_integer_preserves_nonzero_inst`, so we need it defined explicitly.
-/
instance nonzero_one_inst : AP ((1 : ℚ) ≄ 0) := AP.mk nonzero_one

end Lean4Axiomatic.Rational
