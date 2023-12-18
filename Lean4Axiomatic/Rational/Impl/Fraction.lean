import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction.Exponentiation
import Lean4Axiomatic.Rational.Impl.Fraction.Sign
import Lean4Axiomatic.Rational.Impl.Generic.Metric
import Lean4Axiomatic.Rational.Impl.Generic.MinMax
import Lean4Axiomatic.Rational.Impl.Generic.Order

/-! # Formal fraction implementation of rational numbers -/

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable
  {ℕ : Type} [Natural ℕ] [Natural.Induction.{1} ℕ]
  {ℤ : Type} [Integer (ℕ := ℕ) ℤ] [Integer.Induction.{1} ℤ]

instance rational : Rational (ℤ := ℤ) (Fraction ℤ) :=
  let order := Generic.order

  {
    toCore := core
    toAddition := addition
    toMultiplication := multiplication
    toNaturalExponentiation := natural_exponentiation
    toNegation := negation
    toSubtraction := subtraction
    toReciprocation := reciprocation
    toDivision := division
    toSign := sign
    toIntegerExponentiation := integer_exponentiation
    toOrder := order
    toMinMax := Generic.minmax
    toMetric := Generic.metric
  }

end Lean4Axiomatic.Rational.Impl.Fraction
