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

instance rational : Rational (Fraction ℤ) := {
  eqvOp := tildeDash (ℕ := ℕ) (ℤ := ℤ)
}

end Fraction

end Lean4Axiomatic.Rational.Impl
