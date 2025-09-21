import Lean4Axiomatic.Rational.Impl.Fraction.Multiplication
import Lean4Axiomatic.Rational.Negation

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Negation and subtraction on fractions -/

/-- Negation of fractions. -/
def neg : Fraction ℤ → Fraction ℤ
| p//q => (-p)//q

instance negation_ops : Negation.Ops (Fraction ℤ) := {
  neg := neg
}

/--
Negation of integer fractions is consistent with its equivalent on integers.

**Property intuition**: This must be true if we want integers to be represented
as integer fractions.

**Proof intuition**: Follows directly from the definition of negation.
-/
theorem neg_compat_from_integer
    {a : ℤ} : from_integer (-a) ≃ -(from_integer a)
    := calc
  _ = from_integer (-a) := rfl
  _ = (-a)//1           := rfl
  _ = -(a//1)           := rfl
  _ = -(from_integer a) := rfl
  _ ≃ -(from_integer a) := eqv_refl

/--
The negations of equivalent fractions are themselves equivalent.

**Property intuition**: This must be true for negation on fractions to be a
valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
@[gcongr]
theorem neg_subst {p₁ p₂ : Fraction ℤ} : p₁ ≃ p₂ → -p₁ ≃ -p₂ := by
  revert p₁; intro (p₁n//p₁d); let p₁ := p₁n//p₁d
  revert p₂; intro (p₂n//p₂d); let p₂ := p₂n//p₂d
  intro (_ : p₁ ≃ p₂)
  show -p₁ ≃ -p₂

  have : p₁n//p₁d ≃ p₂n//p₂d := ‹p₁ ≃ p₂›
  have : p₁n * p₂d ≃ p₂n * p₁d := ‹p₁n//p₁d ≃ p₂n//p₂d›
  have : -p₁n * p₂d ≃ -p₂n * p₁d := calc
    _ = (-p₁n) * p₂d   := rfl
    _ ≃ (-(p₁n * p₂d)) := Rel.symm AA.scompatL
    _ ≃ (-(p₂n * p₁d)) := by srw [‹p₁n * p₂d ≃ p₂n * p₁d›]
    _ ≃ (-p₂n) * p₁d   := AA.scompatL
  calc
    _ = -p₁         := rfl
    _ = -(p₁n//p₁d) := rfl
    _ = (-p₁n//p₁d) := rfl
    _ ≃ (-p₂n//p₂d) := ‹-p₁n * p₂d ≃ -p₂n * p₁d›
    _ = -(p₂n//p₂d) := rfl
    _ = -p₂         := rfl

/--
The negation of a fraction is its left additive inverse.

**Property intuition**: Fractions should obey all the algebraic properties of
integers.

**Proof intuition**: The denominators are the same, so the numerators can be
directly added. But the numerators are additive inverses, so they sum to zero,
and thus the entire result is zero.
-/
theorem add_inverseL {p : Fraction ℤ} : -p + p ≃ 0 := by
  revert p; intro (pn//pd); let p := pn//pd
  show -p + p ≃ 0
  calc
    _ = -p + p             := rfl
    _ = -(pn//pd) + pn//pd := rfl
    _ = (-pn)//pd + pn//pd := rfl
    _ ≃ (-pn + pn)//pd     := add_eqv_denominators
    _ ≃ 0//pd              := by srw [Integer.neg_invL]
    _ ≃ 0                  := eqv_zero_iff_numerator_eqv_zero.mpr Rel.refl

/--
The negation of a fraction is its right additive inverse.

**Property intuition**: Fractions should obey all the algebraic properties of
integers.

**Proof intuition**: Follows from the left additive inverse and commutativity.
-/
theorem add_inverseR {p : Fraction ℤ} : p + -p ≃ 0 :=
  eqv_trans add_comm add_inverseL

instance negation_props : Negation.Props (Fraction ℤ) := {
  neg_subst := neg_subst
  neg_compat_from_integer := neg_compat_from_integer
  add_inverseL := add_inverseL
  add_inverseR := add_inverseR
}

instance negation : Negation (Fraction ℤ) := {
  toOps := negation_ops
  toProps := negation_props
}

/--
Subtraction of fractions.

**Definition intuition**: Adding the negation is the same as subtraction, e.g.
`5 - 3` is the same as `5 + (-3)`.
-/
def sub (p q : Fraction ℤ) : Fraction ℤ := p + (-q)

instance subtraction_ops : Subtraction.Ops (Fraction ℤ) := {
  sub := sub
}

instance subtraction_props : Subtraction.Props (Fraction ℤ) := {
  sub_add_neg := eqv_refl
}

instance subtraction : Subtraction (Fraction ℤ) := {
  toOps := subtraction_ops
  toProps := subtraction_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
