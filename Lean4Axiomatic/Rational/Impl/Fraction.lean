import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction.Addition
import Lean4Axiomatic.Rational.Impl.Fraction.Inverse
import Lean4Axiomatic.Rational.Impl.Fraction.Multiplication

/-! # Formal fraction implementation of rational numbers -/

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

instance rational : Rational (Fraction ℤ) := {
  toEquivalence := equivalence
  toAddition := addition
  toMultiplication := multiplication
  toNegation := negation
}

end Lean4Axiomatic.Rational.Impl.Fraction
