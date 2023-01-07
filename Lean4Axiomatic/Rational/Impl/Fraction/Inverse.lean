import Lean4Axiomatic.Rational.Impl.Fraction.Multiplication
import Lean4Axiomatic.Rational.Inverse

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Integer (sgn)
open Logic (AP)
open Signed (Negative Positive)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Inverse operations on fractions -/

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
    := by
  show (-a)//1 ≃ -(a//1)
  exact eqv_refl

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
    (-pn + pn)//pd     ≃ _ := substN AA.inverseL
    0//pd              ≃ _ := eqv_zero_iff_numerator_eqv_zero.mpr Rel.refl
    0                  ≃ _ := eqv_refl

/--
Subtraction of fractions.

**Definition intuition**: Adding the negation is the same as subtraction, e.g.
`5 - 3` is the same as `5 + (-3)`.
-/
def sub (p q : Fraction ℤ) : Fraction ℤ := p + (-q)

/-- Provides the `· - ·` notation for subtraction. -/
instance sub_inst : Sub (Fraction ℤ) := {
  sub := sub
}

/--
The negation of a fraction is its right additive inverse.

**Property intuition**: Fractions should obey all the algebraic properties of
integers.

**Proof intuition**: Follows from the left additive inverse and commutativity.
-/
theorem add_inverseR {p : Fraction ℤ} : p + -p ≃ 0 :=
  eqv_trans add_comm add_inverseL

instance negation_props
    : Negation.Props (ℚ := Fraction ℤ) (core_ops := core_ops)
    := {
  neg_subst := neg_subst
  neg_compat_from_integer := neg_compat_from_integer
}

instance negation : Negation (ℚ := Fraction ℤ) (core_ops := core_ops) := {
  toOps := negation_ops
  toProps := negation_props
}

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

instance reciprocation_ops
    : Reciprocation.Ops (ℚ := Fraction ℤ) (core_ops := core_ops)
    := {
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
theorem recip_subst
    {p₁ p₂ : Fraction ℤ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹
    := by
  revert p₁; intro (a//b); revert p₂; intro (c//d)
  intro _ _ (_ : a//b ≃ c//d)
  show (a//b)⁻¹ ≃ (c//d)⁻¹
  have : Integer.Nonzero a := nonzero_numerator (a//b)
  have : Integer.Nonzero c := nonzero_numerator (c//d)
  show (b * sgn a)//(a * sgn a) ≃ (d * sgn c)//(c * sgn c)
  show (b * sgn a) * (c * sgn c) ≃ (d * sgn c) * (a * sgn a)
  have : a * d ≃ c * b := ‹a//b ≃ c//d›
  calc
    (b * sgn a) * (c * sgn c) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (b * c) * (sgn a * sgn c) ≃ _ := AA.substL AA.comm
    (c * b) * (sgn a * sgn c) ≃ _ := AA.substL (Rel.symm ‹a * d ≃ c * b›)
    (a * d) * (sgn a * sgn c) ≃ _ := AA.substL AA.comm
    (d * a) * (sgn a * sgn c) ≃ _ := AA.substR AA.comm
    (d * a) * (sgn c * sgn a) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (d * sgn c) * (a * sgn a) ≃ _ := Rel.refl

/--
The reciprocal of a nonzero fraction is its left multiplicative inverse.

**Property and proof intuition**: Multiplying a fraction by its reciprocal puts
the same factors in the numerator and denominator. They all cancel, giving the
result `1`.
-/
theorem recip_inverseL {p : Fraction ℤ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1 := by
  revert p; intro (pn//pd) (_ : AP (pn//pd ≄ 0))
  show (pn//pd)⁻¹ * pn//pd ≃ 1
  have : Integer.Nonzero pn := nonzero_numerator (pn//pd)
  calc
    (pn//pd)⁻¹ * pn//pd
      ≃ _ := eqv_refl
    (pd * sgn pn)//(pn * sgn pn) * pn//pd
      ≃ _ := eqv_refl
    ((pd * sgn pn) * pn)//((pn * sgn pn) * pd)
      ≃ _ := substN AA.assoc
    (pd * (sgn pn * pn))//((pn * sgn pn) * pd)
      ≃ _ := substN (AA.substR AA.comm)
    (pd * (pn * sgn pn))//((pn * sgn pn) * pd)
      ≃ _ := substN AA.comm
    ((pn * sgn pn) * pd)//((pn * sgn pn) * pd)
      ≃ _ := eqv_one_iff_numer_eqv_denom.mpr Rel.refl
    1
      ≃ _ := eqv_refl

/--
The reciprocal of a nonzero fraction is its right multiplicative inverse.

**Property and proof intuition**: Follows from commutativity of multiplication
and the reciprocal being the left multiplicative inverse.
-/
theorem recip_inverseR {p : Fraction ℤ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1 :=
  eqv_trans mul_comm recip_inverseL

/--
Division of fractions.

**Definition intuition**: Multiplying by the reciprocal is the same as
division, e.g. `2 / 3` is the same as `2 * (1 / 3)`.
-/
def div (p q : Fraction ℤ) [AP (q ≄ 0)] : Fraction ℤ := p * q⁻¹

infixl:70 " / " => div

instance reciprocation
    : Reciprocation (ℚ := Fraction ℤ) (core_ops := core_ops)
    := {
  toOps := reciprocation_ops
}

instance inverse : Inverse (ℚ := Fraction ℤ) (core_ops := core_ops) := {
  toNegation := negation
  toReciprocation := reciprocation
}

end Lean4Axiomatic.Rational.Impl.Fraction
