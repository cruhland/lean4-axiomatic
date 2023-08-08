import Lean4Axiomatic.Natural.Impl.Generic
import Lean4Axiomatic.Rational
import Lean4Axiomatic.Rational.Impl.Fraction.Reciprocation
import Lean4Axiomatic.Rational.Impl.Fraction.Sign
import Lean4Axiomatic.Rational.Impl.Generic.Metric
import Lean4Axiomatic.Rational.Impl.Generic.MinMax
import Lean4Axiomatic.Rational.Impl.Generic.Order

/-! # Formal fraction implementation of rational numbers -/

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable
  {ℕ ℤ : Type} [Natural ℕ] [Natural.Induction.{1} ℕ] [Integer (ℕ := ℕ) ℤ]

instance rational : Rational (ℤ := ℤ) (Fraction ℤ) :=
  let order := Generic.order

  {
    toCore := core
    toAddition := addition
    toMultiplication := multiplication
    toExponentiation := Natural.Impl.Generic.exponentiation
    toNegation := negation
    toSubtraction := subtraction
    toReciprocation := reciprocation
    toDivision := division
    toSign := sign
    toOrder := order
    toMinMax := Generic.minmax
    toMetric := Generic.metric
  }

end Lean4Axiomatic.Rational.Impl.Fraction
