import Lean4Axiomatic.Rational.Impl.Fraction.Multiplication

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer ℕ ℤ]

/-! ## Inverse operations on fractions -/

/-- Negation of fractions. -/
def neg : Fraction ℤ → Fraction ℤ
| p//q => (-p)//q

instance negOp : Neg (Fraction ℤ) := {
  neg := neg
}

/--
The negations of equivalent fractions are themselves equivalent.

**Property intuition**: This must be true for negation on fractions to be a
valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
theorem neg_subst {p₁ p₂ : Fraction ℤ} : p₁ ≃ p₂ → -p₁ ≃ -p₂ := by
  revert p₁; intro (p₁n//p₁d); revert p₂; intro (p₂n//p₂d)
  intro (_ : p₁n//p₁d ≃ p₂n//p₂d)
  show -(p₁n//p₁d) ≃ -(p₂n//p₂d)
  show (-p₁n//p₁d) ≃ (-p₂n//p₂d)
  show -p₁n * p₂d ≃ -p₂n * p₁d
  have : p₁n * p₂d ≃ p₂n * p₁d := ‹p₁n//p₁d ≃ p₂n//p₂d›
  calc
    (-p₁n) * p₂d   ≃ _ := Rel.symm AA.scompatL
    (-(p₁n * p₂d)) ≃ _ := AA.subst₁ ‹p₁n * p₂d ≃ p₂n * p₁d›
    (-(p₂n * p₁d)) ≃ _ := AA.scompatL
    (-p₂n) * p₁d   ≃ _ := Rel.refl

/--
The negation of a fraction is its left additive inverse.

**Property intuition**: Fractions should obey all the algebraic properties of
integers.

**Proof intuition**: The denominators are the same, so the numerators can be
directly added. But the numerators are additive inverses, so they sum to zero,
and thus the entire result is zero.
-/
theorem add_inverseL {p : Fraction ℤ} : -p + p ≃ 0 := by
  revert p; intro (pn//pd)
  show -(pn//pd) + pn//pd ≃ 0
  calc
    -(pn//pd) + pn//pd ≃ _ := eqv_refl
    (-pn)//pd + pn//pd ≃ _ := add_eqv_denominators
    (-pn + pn)//pd     ≃ _ := substL AA.inverseL
    0//pd              ≃ _ := eqv_zero_iff_numerator_eqv_zero.mpr Rel.refl
    0                  ≃ _ := eqv_refl

/--
The negation of a fraction is its right additive inverse.

**Property intuition**: Fractions should obey all the algebraic properties of
integers.

**Proof intuition**: Follows from the left additive inverse and commutativity.
-/
theorem add_inverseR {p : Fraction ℤ} : p + -p ≃ 0 :=
  eqv_trans add_comm add_inverseL

/-- Class providing evidence that a fraction is not zero. -/
class Nonzero (p : Fraction ℤ) :=
  /-- A fraction is nonzero if and only if its numerator is nonzero. -/
  [numerator_nonzero : Integer.Nonzero p.numerator]

/- Automatically derive `Fraction.Nonzero` from `Integer.Nonzero`. -/
attribute [instance] Nonzero.mk

/--
Reciprocal of a fraction.

Has a `Nonzero` constraint because the numerator must be nonzero to become the
denominator.
-/
def reciprocal (p : Fraction ℤ) [Nonzero p] : Fraction ℤ := by
  revert p; intro (a//b) (_ : Nonzero (a//b))
  have : Integer.Nonzero a := ‹Nonzero (a//b)›.numerator_nonzero
  exact b//a

postfix:120 "⁻¹" => reciprocal

/--
The reciprocal operation preserves equivalence.

**Property intuition**: This must be true for reciprocal to be a valid function
on fractions.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Combine these with algebra to
finish the proof.
-/
theorem recip_subst
    {p₁ p₂ : Fraction ℤ} [Nonzero p₁] [Nonzero p₂] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹
    := by
  revert p₁; intro (a//b); revert p₂; intro (c//d)
  intro _ _ (_ : a//b ≃ c//d)
  show (a//b)⁻¹ ≃ (c//d)⁻¹
  have : Integer.Nonzero a := ‹Nonzero (a//b)›.numerator_nonzero
  have : Integer.Nonzero c := ‹Nonzero (c//d)›.numerator_nonzero
  show b//a ≃ d//c
  show b * c ≃ d * a
  have : a * d ≃ c * b := ‹a//b ≃ c//d›
  calc
    b * c ≃ _ := AA.comm
    c * b ≃ _ := Rel.symm ‹a * d ≃ c * b›
    a * d ≃ _ := AA.comm
    d * a ≃ _ := Rel.refl

end Lean4Axiomatic.Rational.Impl.Fraction
