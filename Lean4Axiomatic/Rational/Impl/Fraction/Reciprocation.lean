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
theorem mul_inverseL {p : Fraction ℤ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1 := by
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
  have : Integer.Nonzero a := Integer.nonzero_from_positive_inst
  have : a ≄ 0 := Integer.nonzero_iff_neqv_zero.mp this
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
  have x_sgn_a {x : ℤ} : x * sgn a ≃ x := calc
    x * sgn a ≃ _ := AA.substR ‹sgn a ≃ 1›
    x * 1     ≃ _ := AA.identR
    x         ≃ _ := Rel.refl
  calc
    (a//b)⁻¹                 ≃ _ := eqv_refl
    (b * sgn a)//(a * sgn a) ≃ _ := substN x_sgn_a
    b//(a * sgn a)           ≃ _ := substD x_sgn_a
    b//a                     ≃ _ := eqv_refl

/--
Division of fractions.

**Definition intuition**: Multiplying by the reciprocal is the same as
division, e.g. `2 / 3` is the same as `2 * (1 / 3)`.
-/
def div (p q : Fraction ℤ) [AP (q ≄ 0)] : Fraction ℤ := p * q⁻¹

instance division_ops : Division.Ops (Fraction ℤ) := {
  div := div
}

/--
Converting two integers to fractions and then dividing them is equivalent to
forming a fraction directly from the integers.

**Property intuition**: Making this property true is one of the reasons for
introducing formal fractions to begin with: to have a consistent inverse of
multiplication for integers.

**Proof intuition**: Expanding the defintions of fractions and division, and
then simplifying via algebraic identities, gives the result.
-/
theorem div_eqv_fraction
    {a b : ℤ} [AP (Positive b)] : (a : Fraction ℤ) / b ≃ a//b
    := calc
  (a : Fraction ℤ) / b ≃ _ := eqv_refl
  (a//1) / (b//1)      ≃ _ := eqv_refl
  (a//1) * (b//1)⁻¹    ≃ _ := mul_substR recip_positive
  (a//1) * (1//b)      ≃ _ := eqv_refl
  (a * 1)//(1 * b)     ≃ _ := substN AA.identR
  a//(1 * b)           ≃ _ := substD AA.identL
  a//b                 ≃ _ := eqv_refl

/--
Every fraction satisfies the rational induction axiom, that is
if a predicate holds for all formal fractions of the form a / b,
with a and b being integers, then it holds for all formal fractions.

**Property intuition**: When a and b are integers and b ≠ 0, they can be
converted/coerced to formal fractions f_1 = a // 1 and f_2 = b // 1 
via function from_integer. Dividing, we have f_1 / f_2 ≃ a // b. Since
formal fractions are just expressions of this form, it follows that if a
predicate holds for all such expressions (a / b), it should hold for all
formal fractions, that is all elements of (Fraction ℤ).  Note (a / b) is the
same as ((from_integer a) / (from_integer b)), since coercion happens
implicitly. Technically, this result is guarenteed only for predicates that are
compatible/substitive with respect to the equivalence relation ≃.

**Proof intuition**: Expand the definitions of formal fractions, division on
them, and the previous fundamental result div_eqv_fraction, to show that an 
arbitrary formal fraction a//b ≃ (a : Fraction ℤ) / b. Now if a predicate
(called motive below) holds for all expression like (a : Fraction ℤ) / b and
it is compatible with ≃ (see motive_subst below), then clearly it holds for
all formal fractions, specifically all elements of (Fraction ℤ).
--/
def ind_fraction {motive : (Fraction ℤ) → Prop} 
  [motive_subst : AA.Substitutive₁ (α := (Fraction ℤ)) motive (· ≃ ·) (· → ·)]
  : ({a b : ℤ} → [Integer.Nonzero b] → motive (a / b)) → (p : (Fraction ℤ)) →
  motive p := by
  intro ind_on_motive p; revert p; intro (a//b)
  have b_not_zero : Integer.Nonzero b := Integer.nonzero_from_positive_inst
  have ind_division : motive (a / b) := @ind_on_motive a b b_not_zero
  have : motive (a//b) := motive_subst.subst₁ div_eqv_fraction ind_division
  exact this

instance division_props : Division.Props (Fraction ℤ) := {
  div_mul_recip := eqv_refl
  ind_fraction := ind_fraction
}

instance division : Division (Fraction ℤ) := {
  toOps := division_ops
  toProps := division_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
