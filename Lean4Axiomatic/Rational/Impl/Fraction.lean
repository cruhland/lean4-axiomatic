import Lean4Axiomatic.Integer
import Lean4Axiomatic.Rational

namespace Lean4Axiomatic.Rational.Impl

/--
Formal fractions over a type `α`.

Think of this type as an "unevaluated" division operation.
-/
structure Fraction (α : Type) : Type :=
  numerator : α
  denominator : α

infix:90 "//" => Fraction.mk

namespace Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer ℕ ℤ]

/--
Equivalence relation on rational numbers (i.e., fractions of integers).

Based on the fundamental notion that fractions represent division, the inverse
of multiplication. Informally, we want the following line of reasoning to hold:
1. `p//q ≃ r//s`
1. `(p//q) * q ≃ (r//s) * q`
1. `p ≃ (r * q)//s`
1. `p * s ≃ ((r * q)//s) * s`
1. `p * s ≃ r * q`
-/
def eqv : Fraction ℤ → Fraction ℤ → Prop
| p//q, r//s => p * s ≃ r * q

instance tildeDash : Operators.TildeDash (Fraction ℤ) := {
  tildeDash := eqv (ℕ := ℕ) (ℤ := ℤ)
}

/-- Integer fraction equivalence is reflexive. -/
theorem eqv_refl {p : Fraction ℤ} : p ≃ p := by
  revert p; intro (a//b)
  show a//b ≃ a//b
  show a * b ≃ a * b
  exact Rel.refl

/-- Integer fraction equivalence is symmetric. -/
theorem eqv_symm {p q : Fraction ℤ} : p ≃ q → q ≃ p := by
  revert p; intro (a//b); revert q; intro (c//d)
  intro (_ : a//b ≃ c//d)
  show c//d ≃ a//b
  have : a * d ≃ c * b := ‹a//b ≃ c//d›
  show c * b ≃ a * d
  exact Rel.symm ‹a * d ≃ c * b›

/--
Integer fraction equivalence is transitive.

**Proof intuition**: The assumptions almost allow us to prove the goal
equivalence, but both sides have `q.denominator` as an extra factor. Cancel it
out (because it's nonzero) to finish the proof.
-/
theorem eqv_trans
    {p q r : Fraction ℤ} : q.denominator ≄ 0 → p ≃ q → q ≃ r → p ≃ r
    := by
  revert p; intro (pn//pd); revert q; intro (qn//qd); revert r; intro (rn//rd)
  intro (_ : qd ≄ 0) (_ : pn//pd ≃ qn//qd) (_ : qn//qd ≃ rn//rd)
  show pn//pd ≃ rn//rd
  have : pn * qd ≃ qn * pd := ‹pn//pd ≃ qn//qd›
  have : qn * rd ≃ rn * qd := ‹qn//qd ≃ rn//rd›
  show pn * rd ≃ rn * pd
  have : (pn * rd) * qd ≃ (rn * pd) * qd := calc
    (pn * rd) * qd ≃ _ := AA.substL AA.comm
    (rd * pn) * qd ≃ _ := AA.assoc
    rd * (pn * qd) ≃ _ := AA.substR ‹pn * qd ≃ qn * pd›
    rd * (qn * pd) ≃ _ := Rel.symm AA.assoc
    (rd * qn) * pd ≃ _ := AA.substL AA.comm
    (qn * rd) * pd ≃ _ := AA.substL ‹qn * rd ≃ rn * qd›
    (rn * qd) * pd ≃ _ := AA.assoc
    rn * (qd * pd) ≃ _ := AA.substR AA.comm
    rn * (pd * qd) ≃ _ := Rel.symm AA.assoc
    (rn * pd) * qd ≃ _ := Rel.refl
  have : pn * rd ≃ rn * pd :=
    Integer.mul_cancelR ‹qd ≄ 0› ‹(pn * rd) * qd ≃ (rn * pd) * qd›
  exact this

instance rational : Rational (Fraction ℤ) := {
  eqvOp := tildeDash (ℕ := ℕ) (ℤ := ℤ)
}

end Fraction

end Lean4Axiomatic.Rational.Impl
