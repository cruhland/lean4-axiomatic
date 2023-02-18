import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction.Reciprocation
import Lean4Axiomatic.Rational.Impl.Fraction.Sign

/-! # Formal fraction implementation of rational numbers -/

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

instance rational : Rational (ℤ := ℤ) (Fraction ℤ) := {
  toCore := core
  toAddition := addition
  toMultiplication := multiplication
  toNegation := negation
  toSubtraction := subtraction
  toReciprocation := reciprocation
  toDivision := division
  toSign := sign
}

end Lean4Axiomatic.Rational.Impl.Fraction
