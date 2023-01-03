import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction.Inverse

/-! # Formal fraction implementation of rational numbers -/

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

instance rational : Rational (ℤ := ℤ) (Fraction ℤ) := {
  toCore := core
  toAddition := addition
  toMultiplication := multiplication
  toNegation := negation
}

end Lean4Axiomatic.Rational.Impl.Fraction
