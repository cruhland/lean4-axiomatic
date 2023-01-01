import Lean4Axiomatic.Rational.Addition
import Lean4Axiomatic.Rational.Core
import Lean4Axiomatic.Rational.Multiplication

/-! # Rational numbers -/

namespace Lean4Axiomatic

/-! ## Axioms -/

/--
The class of [rational numbers](https://en.wikipedia.org/wiki/Rational_number).

Provides fundamental operations and properties that any type implementing the
rational numbers must have.
-/
class Rational (ℚ : Type) :=
  toEquivalence : Rational.Equivalence ℚ
  toAddition : Rational.Addition ℚ
  toMultiplication : Rational.Multiplication ℚ

  /-- Negation of rational numbers. -/
  negOp : Neg ℚ

end Lean4Axiomatic
