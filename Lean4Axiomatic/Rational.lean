import Lean4Axiomatic.Rational.Sign

/-! # Rational numbers -/

namespace Lean4Axiomatic

/-! ## Axioms -/

/--
The class of [rational numbers](https://en.wikipedia.org/wiki/Rational_number).

Provides fundamental operations and properties that any type implementing the
rational numbers must have. They are broken out into subclasses to keep them
better organized.
-/
class Rational
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ] (ℚ : Type)
    :=
  toCore : Rational.Core (ℤ := ℤ) ℚ
  toAddition : Rational.Addition ℚ
  toMultiplication : Rational.Multiplication ℚ
  toInverse : Rational.Inverse ℚ
  toSign : Rational.Sign ℚ

end Lean4Axiomatic
