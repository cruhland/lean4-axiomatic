module
public import Lean4Axiomatic.Natural.Impl.Generic
public import Lean4Axiomatic.Rational
public import Lean4Axiomatic.Rational.Impl.Fraction.Sign
public import Lean4Axiomatic.Rational.Impl.Fraction.Induction
public import Lean4Axiomatic.Rational.Impl.Generic.Exponentiation
public import Lean4Axiomatic.Rational.Impl.Generic.FloorCeil
public import Lean4Axiomatic.Rational.Impl.Generic.Metric
public import Lean4Axiomatic.Rational.Impl.Generic.MinMax
public import Lean4Axiomatic.Rational.Impl.Generic.Order

@[expose] public section

/-! # Formal fraction implementation of rational numbers -/

namespace Lean4Axiomatic.Rational.Impl.Fraction

variable
  {ℕ : Type} [Natural ℕ] [Natural.Induction.{1} ℕ]
  {ℤ : Type} [Integer (ℕ := ℕ) ℤ] [Integer.Induction.{1} ℤ]

instance rational : Rational (ℤ := ℤ) (Fraction ℤ) :=
  let induction₁ := induction.{1}
  let order := Generic.order
  let natural_exponentiation := Natural.Impl.Generic.exponentiation

  {
    toCore := core
    toAddition := addition
    toMultiplication := multiplication
    toNaturalExponentiation := natural_exponentiation
    toNegation := negation
    toSubtraction := subtraction
    toReciprocation := reciprocation
    toDivision := division
    toInduction₀ := induction
    toInduction₁ := induction₁
    toSign := sign
    toIntegerExponentiation := Generic.integer_exponentiation
    toOrder := order
    toMinMax := Generic.minmax
    toMetric := Generic.metric
    toFloorCeil := Generic.floor_ceil
  }

end Lean4Axiomatic.Rational.Impl.Fraction
