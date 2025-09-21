import Lean4Axiomatic.Rational.Impl.Fraction.Multiplication
import Lean4Axiomatic.Rational.Reciprocation

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Logic (AP)
open Signed (Positive sgn)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Reciprocation and division on fractions -/

/--
Reciprocal of a fraction.

Requires the fraction to be nonzero because its numerator will become the
denominator of the reciprocal. The new denominator can be made positive by
multiplying it by its own `sgn` value. The nonzero requirement is an instance
argument so that usages of the `·⁻¹` syntax don't need to explicitly pass it.
-/
def reciprocal (p : Fraction ℤ) [AP (p ≄ 0)] : Fraction ℤ := by
  revert p; intro (a//b) (_ : AP (a//b ≄ 0))
  have : Integer.Nonzero a := nonzero_numerator (a//b)
  have : AP (Positive (a * sgn a)) := Integer.positive_mul_sgn_self_inst
  exact (b * sgn a)//(a * sgn a)

instance reciprocation_ops : Reciprocation.Ops (Fraction ℤ) := {
  reciprocal := reciprocal
}

/--
The reciprocal operation preserves equivalence.

**Property intuition**: This must be true for reciprocal to be a valid function
on fractions.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Combine these with algebra to
finish the proof.
-/
@[gcongr]
theorem recip_subst
    {p₁ p₂ : Fraction ℤ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹
    := by
  revert p₁; intro (a//b); let p₁ := a//b
  revert p₂; intro (c//d); let p₂ := c//d
  intro _ _ (_ : p₁ ≃ p₂)
  show p₁⁻¹ ≃ p₂⁻¹

  have : a//b ≃ c//d := ‹p₁ ≃ p₂›
  have : a * d ≃ c * b := ‹a//b ≃ c//d›
  have : (b * sgn a) * (c * sgn c) ≃ (d * sgn c) * (a * sgn a) := calc
    _ = (b * sgn a) * (c * sgn c) := rfl
    _ ≃ (b * c) * (sgn a * sgn c) := AA.expr_xxfxxff_lr_swap_rl
    _ ≃ (c * b) * (sgn a * sgn c) := by srw [AA.comm]
    _ ≃ (a * d) * (sgn a * sgn c) := by srw [←‹a * d ≃ c * b›]
    _ ≃ (d * a) * (sgn a * sgn c) := by srw [AA.comm]
    _ ≃ (d * a) * (sgn c * sgn a) := by srw [AA.comm]
    _ ≃ (d * sgn c) * (a * sgn a) := AA.expr_xxfxxff_lr_swap_rl

  have : Integer.Nonzero a := nonzero_numerator p₁
  have : Integer.Nonzero c := nonzero_numerator p₂
  calc
    _ = p₁⁻¹                     := rfl
    _ = (a//b)⁻¹                 := rfl
    _ = (b * sgn a)//(a * sgn a) := rfl
    _ ≃ (d * sgn c)//(c * sgn c) := ‹(b*sgn a)*(c*sgn c) ≃ (d*sgn c)*(a*sgn a)›
    _ = (c//d)⁻¹                 := rfl
    _ = p₂⁻¹                     := rfl

/--
The reciprocal of a nonzero fraction is its left multiplicative inverse.

**Property and proof intuition**: Multiplying a fraction by its reciprocal puts
the same factors in the numerator and denominator. They all cancel, giving the
result `1`.
-/
theorem mul_inverseL {p : Fraction ℤ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1 := by
  revert p; intro (pn//pd); let p := pn//pd; intro (_ : AP (p ≄ 0))
  show p⁻¹ * p ≃ 1

  have : Integer.Nonzero pn := nonzero_numerator p
  have num_denom_same {a : ℤ} [AP (Positive a)] : a//a ≃ 1 :=
    eqv_one_iff_numer_eqv_denom.mpr Rel.refl

  calc
    _ = p⁻¹ * p                                    := rfl
    _ = (pn//pd)⁻¹ * pn//pd                        := rfl
    _ = (pd * sgn pn)//(pn * sgn pn) * pn//pd      := rfl
    _ = ((pd * sgn pn) * pn)//((pn * sgn pn) * pd) := rfl
    _ ≃ (pd * (sgn pn * pn))//((pn * sgn pn) * pd) := by srw [AA.assoc]
    _ ≃ (pd * (pn * sgn pn))//((pn * sgn pn) * pd) := by srw [AA.comm]
    _ ≃ ((pn * sgn pn) * pd)//((pn * sgn pn) * pd) := by srw [AA.comm]
    _ ≃ 1                                          := num_denom_same

/--
The reciprocal of a nonzero fraction is its right multiplicative inverse.

**Property and proof intuition**: Follows from commutativity of multiplication
and the reciprocal being the left multiplicative inverse.
-/
theorem mul_inverseR {p : Fraction ℤ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1 :=
  eqv_trans mul_comm mul_inverseL

instance reciprocation_props : Reciprocation.Props (Fraction ℤ) := {
  recip_subst := recip_subst
  mul_inverseL := mul_inverseL
  mul_inverseR := mul_inverseR
}

instance reciprocation : Reciprocation (Fraction ℤ) := {
  toOps := reciprocation_ops
  toProps := reciprocation_props
}

/--
A fraction with a positive numerator is not equivalent to zero.

This is a trivial lemma to enable the instance version below.

**Property and proof intuition**: We already know that fractions with nonzero
numerators are not equivalent to zero; a positive numerator is nonzero.
-/
theorem nonzero_from_positive_numer
    {a b : ℤ} [AP (Positive a)] [AP (Positive b)] : a//b ≄ 0
    := by
  have : a ≄ 0 := Integer.neqv_zero_from_positive ‹AP (Positive a)›.ev
  have : a//b ≄ 0 := mt eqv_zero_iff_numerator_eqv_zero.mp this
  exact this

/--
This instance exists to allow a clean syntax for the reciprocal in
`recip_positive`.
-/
instance nonzero_from_positive_numer_inst
    {a b : ℤ} [AP (Positive a)] [AP (Positive b)] : AP (a//b ≄ 0)
    :=
  AP.mk nonzero_from_positive_numer

/--
The reciprocal of a fraction with a positive numerator simply swaps the
numerator and denominator.

**Property intuition**: The denominator of our fractions must be positive, so
if the numerator is already positive then no sign correction is needed for it
to become the denominator.

**Proof intuition**: Expand the definition of reciprocal. The `sgn a` terms are
equivalent to `1` and drop out, because `a` is positive.
-/
theorem recip_positive
    {a b : ℤ} [AP (Positive a)] [AP (Positive b)] : (a//b)⁻¹ ≃ b//a
    := by
  have : sgn a ≃ 1 := Integer.sgn_positive.mp ‹AP (Positive a)›.ev
  calc
    _ = (a//b)⁻¹                 := rfl
    _ = (b * sgn a)//(a * sgn a) := rfl
    _ ≃ (b * 1)//(a * sgn a)     := by srw [‹sgn a ≃ 1›]
    _ ≃ (b * 1)//(a * 1)         := by srw [‹sgn a ≃ 1›]
    _ ≃ b//(a * 1)               := by srw [Integer.mul_identR]
    _ ≃ b//a                     := by srw [Integer.mul_identR]

/--
Division of fractions.

**Definition intuition**: Multiplying by the reciprocal is the same as
division, e.g. `2 / 3` is the same as `2 * (1 / 3)`.
-/
def div (p q : Fraction ℤ) [AP (q ≄ 0)] : Fraction ℤ := p * q⁻¹

instance division_ops : Division.Ops (Fraction ℤ) := {
  div := div
}

instance division_props : Division.Props (Fraction ℤ) := {
  div_mul_recip := eqv_refl
}

instance division : Division (Fraction ℤ) := {
  toOps := division_ops
  toProps := division_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
