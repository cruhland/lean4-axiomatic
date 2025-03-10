import Lean4Axiomatic.Rational.Addition
import Lean4Axiomatic.Rational.Impl.Fraction.Core

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Signed (Positive)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Fraction addition -/

/--
Addition of fractions.

Uses naive fraction addition, and the proof that naive fraction addition always
results in a positive denominator if the input denominators are positive.
-/
def add (p q : Fraction ℤ) : Fraction ℤ :=
  let sum := p.naive + q.naive
  have : Positive p.denominator := p.denominator_positive.ev
  have : Positive q.denominator := q.denominator_positive.ev
  have : Positive sum.denominator :=
    Naive.add_preserves_positive_denominators
      ‹Positive p.denominator›
      ‹Positive q.denominator›
  from_naive sum ‹Positive sum.denominator›

instance addition_ops : Addition.Ops (Fraction ℤ) := {
  add := add
}

/--
Addition of integer fractions is consistent with its equivalent on integers.

**Property intuition**: This must be true if we want integers to be represented
as integer fractions.

**Proof intuition**: Expand the definition of addition and use integer algebra
on the numerator and denominator.
-/
theorem add_compat_from_integer
    {a b : ℤ} : from_integer (a + b) ≃ from_integer a + from_integer b
    := by
  show (a + b)//1 ≃ a//1 + b//1
  have : a//1 + b//1 ≃ (a + b)//1 := calc
    a//1 + b//1              ≃ _ := eqv_refl
    (a * 1 + 1 * b)//(1 * 1) ≃ _ := substN (Integer.add_substL AA.identR)
    (a + 1 * b)//(1 * 1)     ≃ _ := substN (Integer.add_substR AA.identL)
    (a + b)//(1 * 1)         ≃ _ := substD AA.identL
    (a + b)//1               ≃ _ := eqv_refl
  exact eqv_symm this

/--
Addition of integer fractions is commutative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Expand the definition of addition and use integer algebra
on the numerator and denominator.
-/
theorem add_comm {p q : Fraction ℤ} : p + q ≃ q + p := by
  revert p; intro (pn//pd); revert q; intro (qn//qd)
  show pn//pd + qn//qd ≃ qn//qd + pn//pd
  calc
    pn//pd + qn//qd                ≃ _ := eqv_refl
    (pn * qd + pd * qn)//(pd * qd) ≃ _ := substN (Integer.add_substL AA.comm)
    (qd * pn + pd * qn)//(pd * qd) ≃ _ := substN (Integer.add_substR AA.comm)
    (qd * pn + qn * pd)//(pd * qd) ≃ _ := substN Integer.add_comm
    (qn * pd + qd * pn)//(pd * qd) ≃ _ := substD AA.comm
    (qn * pd + qd * pn)//(qd * pd) ≃ _ := eqv_refl
    qn//qd + pn//pd                ≃ _ := eqv_refl

/--
Replacing the left operand in a sum of fractions with an equivalent value gives
an equivalent result.

**Property intuition**: This must be true for addition on fractions to be a
valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
theorem add_substL {p₁ p₂ q : Fraction ℤ} : p₁ ≃ p₂ → p₁ + q ≃ p₂ + q := by
  revert p₁; intro (p₁n//p₁d); revert p₂; intro (p₂n//p₂d)
  revert q; intro (qn//qd)
  intro (_ : p₁n//p₁d ≃ p₂n//p₂d)
  show p₁n//p₁d + qn//qd ≃ p₂n//p₂d + qn//qd
  show (p₁n * qd + p₁d * qn)//(p₁d * qd) ≃ (p₂n * qd + p₂d * qn)//(p₂d * qd)
  show (p₁n * qd + p₁d * qn) * (p₂d * qd) ≃ (p₂n * qd + p₂d * qn) * (p₁d * qd)
  have : p₁n * p₂d ≃ p₂n * p₁d := ‹p₁n//p₁d ≃ p₂n//p₂d›
  calc
    (p₁n * qd + p₁d * qn) * (p₂d * qd)
      ≃ _ := Rel.symm AA.assoc
    ((p₁n * qd + p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL AA.distribR
    ((p₁n * qd) * p₂d + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (Integer.add_substL (AA.substL AA.comm))
    ((qd * p₁n) * p₂d + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (Integer.add_substL AA.assoc)
    (qd * (p₁n * p₂d) + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (Integer.add_substL (AA.substR ‹p₁n * p₂d ≃ p₂n * p₁d›))
    (qd * (p₂n * p₁d) + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (Integer.add_substL (Rel.symm AA.assoc))
    ((qd * p₂n) * p₁d + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (Integer.add_substR AA.assoc)
    ((qd * p₂n) * p₁d + p₁d * (qn * p₂d)) * qd
      ≃ _ := AA.substL (Integer.add_substR AA.comm)
    ((qd * p₂n) * p₁d + (qn * p₂d) * p₁d) * qd
      ≃ _ := AA.substL (Rel.symm AA.distribR)
    ((qd * p₂n + qn * p₂d) * p₁d) * qd
      ≃ _ := AA.assoc
    (qd * p₂n + qn * p₂d) * (p₁d * qd)
      ≃ _ := AA.substL (Integer.add_substL AA.comm)
    (p₂n * qd + qn * p₂d) * (p₁d * qd)
      ≃ _ := AA.substL (Integer.add_substR AA.comm)
    (p₂n * qd + p₂d * qn) * (p₁d * qd)
      ≃ _ := Rel.refl

/--
Replacing the right operand in a sum of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for addition on fractions to be a
valid function.

**Proof intuition**: Flip the sum around using commutativity, perform left
substitution, then flip it back.
-/
theorem add_substR {p q₁ q₂ : Fraction ℤ} : q₁ ≃ q₂ → p + q₁ ≃ p + q₂ := by
  intro (_ : q₁ ≃ q₂)
  show p + q₁ ≃ p + q₂
  calc
    p + q₁ ≃ _ := add_comm
    q₁ + p ≃ _ := add_substL ‹q₁ ≃ q₂›
    q₂ + p ≃ _ := add_comm
    p + q₂ ≃ _ := eqv_refl

/--
Fraction addition is associative.

**Property intuition**: Fractions are scaled integers, so we expect
associativity to carry over.

**Proof intuition**: Expand definitions until each side of the equivalence is a
single fraction. The denominators are clearly equivalent by associativity of
integer multiplication. The numerators are equivalent via distributivity, and
associativity of addition, over integers.
-/
theorem add_assoc {p q r : Fraction ℤ} : (p + q) + r ≃ p + (q + r) := by
  revert p; intro (pn//pd); revert q; intro (qn//qd); revert r; intro (rn//rd)
  show (pn//pd + qn//qd) + rn//rd ≃ pn//pd + (qn//qd + rn//rd)
  calc
    (pn//pd + qn//qd) + rn//rd
      ≃ _ := eqv_refl
    (pn * qd + pd * qn)//(pd * qd) + rn//rd
      ≃ _ := eqv_refl
    ((pn * qd + pd * qn) * rd + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substN (Integer.add_substL AA.distribR)
    (((pn * qd) * rd + (pd * qn) * rd) + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substN (Integer.add_substL (Integer.add_substL AA.assoc))
    ((pn * (qd * rd) + (pd * qn) * rd) + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substN (Integer.add_substL (Integer.add_substR AA.assoc))
    ((pn * (qd * rd) + pd * (qn * rd)) + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substN (Integer.add_substR AA.assoc)
    ((pn * (qd * rd) + pd * (qn * rd)) + pd * (qd * rn))//((pd * qd) * rd)
      ≃ _ := substN Integer.add_assoc
    (pn * (qd * rd) + (pd * (qn * rd) + pd * (qd * rn)))//((pd * qd) * rd)
      ≃ _ := substN (Integer.add_substR (Rel.symm AA.distribL))
    (pn * (qd * rd) + pd * (qn * rd + qd * rn))//((pd * qd) * rd)
      ≃ _ := substD AA.assoc
    (pn * (qd * rd) + pd * (qn * rd + qd * rn))//(pd * (qd * rd))
      ≃ _ := eqv_refl
    pn//pd + (qn * rd + qd * rn)//(qd * rd)
      ≃ _ := eqv_refl
    pn//pd + (qn//qd + rn//rd)
      ≃ _ := eqv_refl

/--
Zero is a left identity element for fraction addition.

**Property intuition**: Fractions are scaled integers, so we expect
identity elements to carry over.

**Proof intuition**: Expand definitions, add, and simplify.
-/
theorem add_identL {p : Fraction ℤ} : 0 + p ≃ p := by
  revert p; intro (pn//pd)
  show 0//1 + pn//pd ≃ pn//pd
  calc
    (0 : ℤ)//1 + pn//pd         ≃ _ := eqv_refl
    (0 * pd + 1 * pn)//(1 * pd) ≃ _ := substN (Integer.add_substL AA.absorbL)
    (0 + 1 * pn)//(1 * pd)      ≃ _ := substN AA.identL
    (1 * pn)//(1 * pd)          ≃ _ := substN AA.identL
    pn//(1 * pd)                ≃ _ := substD AA.identL
    pn//pd                      ≃ _ := eqv_refl

/--
Zero is a right identity element for fraction addition.

**Property intuition**: Fractions are scaled integers, so we expect
identity elements to carry over.

**Proof intuition**: Combine commutativity with the left identity proof.
-/
theorem add_identR {p : Fraction ℤ} : p + 0 ≃ p :=
  eqv_trans add_comm add_identL

instance addition_props : Addition.Props (Fraction ℤ) := {
  add_substL := add_substL
  add_substR := add_substR
  add_compat_from_integer := add_compat_from_integer
  add_comm := add_comm
  add_assoc := add_assoc
  add_identL := add_identL
  add_identR := add_identR
}

instance addition : Addition (Fraction ℤ) := {
  toOps := addition_ops
  toProps := addition_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
