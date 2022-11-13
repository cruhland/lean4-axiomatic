import Lean4Axiomatic.Rational.Impl.Fraction.Core

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer ℕ ℤ]

/-! ## Fraction multiplication -/

/-- Multiplication of fractions. -/
def mul : Fraction ℤ → Fraction ℤ → Fraction ℤ
| p//q, r//s => (p * r)//(q * s)

instance mulOp : Mul (Fraction ℤ) := {
  mul := mul
}

/--
Multiplication of fractions is commutative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Expand all definitions in the goal until an equivalence
involving only integers is reached. Show this equivalence using algebra.
-/
theorem mul_comm {p q : Fraction ℤ} : p * q ≃ q * p := by
  revert p; intro (pn//pd); revert q; intro (qn//qd)
  show pn//pd * qn//qd ≃ qn//qd * pn//pd
  show (pn * qn)//(pd * qd) ≃ (qn * pn)//(qd * pd)
  show (pn * qn) * (qd * pd) ≃ (qn * pn) * (pd * qd)
  calc
    (pn * qn) * (qd * pd) ≃ _ := AA.substL AA.comm
    (qn * pn) * (qd * pd) ≃ _ := AA.substR AA.comm
    (qn * pn) * (pd * qd) ≃ _ := Rel.refl

/--
Replacing the left operand in a product of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for multiplication on fractions to be
a valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
theorem mul_substL {p₁ p₂ q : Fraction ℤ} : p₁ ≃ p₂ → p₁ * q ≃ p₂ * q := by
  revert p₁; intro (p₁n//p₁d); revert p₂; intro (p₂n//p₂d)
  revert q; intro (qn//qd)
  intro (_ : p₁n//p₁d ≃ p₂n//p₂d)
  show p₁n//p₁d * qn//qd ≃ p₂n//p₂d * qn//qd
  show (p₁n * qn)//(p₁d * qd) ≃ (p₂n * qn)//(p₂d * qd)
  show (p₁n * qn) * (p₂d * qd) ≃ (p₂n * qn) * (p₁d * qd)
  have : p₁n * p₂d ≃ p₂n * p₁d := ‹p₁n//p₁d ≃ p₂n//p₂d›
  calc
    (p₁n * qn) * (p₂d * qd) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (p₁n * p₂d) * (qn * qd) ≃ _ := AA.substL ‹p₁n * p₂d ≃ p₂n * p₁d›
    (p₂n * p₁d) * (qn * qd) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (p₂n * qn) * (p₁d * qd) ≃ _ := Rel.refl

/--
Replacing the right operand in a product of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for multiplication on fractions to be
a valid function.

**Proof intuition**: Flip the product around using commutativity, perform left
substitution, then flip it back.
-/
theorem mul_substR {p q₁ q₂ : Fraction ℤ} : q₁ ≃ q₂ → p * q₁ ≃ p * q₂ := by
  intro (_ : q₁ ≃ q₂)
  show p * q₁ ≃ p * q₂
  calc
    p * q₁ ≃ _ := mul_comm
    q₁ * p ≃ _ := mul_substL ‹q₁ ≃ q₂›
    q₂ * p ≃ _ := mul_comm
    p * q₂ ≃ _ := eqv_refl

end Lean4Axiomatic.Rational.Impl.Fraction
