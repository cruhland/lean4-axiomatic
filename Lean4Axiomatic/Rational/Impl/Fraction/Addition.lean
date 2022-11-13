import Lean4Axiomatic.Rational.Impl.Fraction.Core

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Integer (Nonzero)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer ℕ ℤ]

/-! ## Fraction addition -/

/--
Addition of fractions.

Uses naive fraction addition, and the proof that naive fraction addition always
results in a nonzero denominator if the input denominators are nonzero.
-/
def add (p q : Fraction ℤ) : Fraction ℤ :=
  let sum := p.naive + q.naive
  have : Nonzero sum.denominator :=
    Naive.add_preserves_nonzero_denominators
      p.denominator_nonzero
      q.denominator_nonzero
  from_naive sum ‹Nonzero sum.denominator›

instance addOp : Add (Fraction ℤ) := {
  add := add
}

/--
Addition of fractions is commutative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Expand all definitions in the goal until an equivalence
involving only integers is reached. Show this equivalence using algebra.
-/
theorem add_comm {p q : Fraction ℤ} : p + q ≃ q + p := by
  revert p; intro (pn//pd); revert q; intro (qn//qd)
  show pn//pd + qn//qd ≃ qn//qd + pn//pd
  show (pn * qd + pd * qn)//(pd * qd) ≃ (qn * pd + qd * pn)//(qd * pd)
  show (pn * qd + pd * qn) * (qd * pd) ≃ (qn * pd + qd * pn) * (pd * qd)
  calc
    (pn * qd + pd * qn) * (qd * pd) ≃ _ := AA.substL (AA.substL AA.comm)
    (qd * pn + pd * qn) * (qd * pd) ≃ _ := AA.substL (AA.substR AA.comm)
    (qd * pn + qn * pd) * (qd * pd) ≃ _ := AA.substL AA.comm
    (qn * pd + qd * pn) * (qd * pd) ≃ _ := AA.substR AA.comm
    (qn * pd + qd * pn) * (pd * qd) ≃ _ := Rel.refl

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
      ≃ _ := AA.substL (AA.substL (AA.substL AA.comm))
    ((qd * p₁n) * p₂d + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (AA.substL AA.assoc)
    (qd * (p₁n * p₂d) + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (AA.substL (AA.substR ‹p₁n * p₂d ≃ p₂n * p₁d›))
    (qd * (p₂n * p₁d) + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (AA.substL (Rel.symm AA.assoc))
    ((qd * p₂n) * p₁d + (p₁d * qn) * p₂d) * qd
      ≃ _ := AA.substL (AA.substR AA.assoc)
    ((qd * p₂n) * p₁d + p₁d * (qn * p₂d)) * qd
      ≃ _ := AA.substL (AA.substR AA.comm)
    ((qd * p₂n) * p₁d + (qn * p₂d) * p₁d) * qd
      ≃ _ := AA.substL (Rel.symm AA.distribR)
    ((qd * p₂n + qn * p₂d) * p₁d) * qd
      ≃ _ := AA.assoc
    (qd * p₂n + qn * p₂d) * (p₁d * qd)
      ≃ _ := AA.substL (AA.substL AA.comm)
    (p₂n * qd + qn * p₂d) * (p₁d * qd)
      ≃ _ := AA.substL (AA.substR AA.comm)
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
      ≃ _ := substL (AA.substL AA.distribR)
    (((pn * qd) * rd + (pd * qn) * rd) + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substL (AA.substL (AA.substL AA.assoc))
    ((pn * (qd * rd) + (pd * qn) * rd) + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substL (AA.substL (AA.substR AA.assoc))
    ((pn * (qd * rd) + pd * (qn * rd)) + (pd * qd) * rn)//((pd * qd) * rd)
      ≃ _ := substL (AA.substR AA.assoc)
    ((pn * (qd * rd) + pd * (qn * rd)) + pd * (qd * rn))//((pd * qd) * rd)
      ≃ _ := substL AA.assoc
    (pn * (qd * rd) + (pd * (qn * rd) + pd * (qd * rn)))//((pd * qd) * rd)
      ≃ _ := substL (AA.substR (Rel.symm AA.distribL))
    (pn * (qd * rd) + pd * (qn * rd + qd * rn))//((pd * qd) * rd)
      ≃ _ := substR AA.assoc
    (pn * (qd * rd) + pd * (qn * rd + qd * rn))//(pd * (qd * rd))
      ≃ _ := eqv_refl
    pn//pd + (qn * rd + qd * rn)//(qd * rd)
      ≃ _ := eqv_refl
    pn//pd + (qn//qd + rn//rd)
      ≃ _ := eqv_refl

end Lean4Axiomatic.Rational.Impl.Fraction
