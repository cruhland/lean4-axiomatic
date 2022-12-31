import Lean4Axiomatic.Rational.Core

/-! # Rational numbers -/

namespace Lean4Axiomatic

/-! ## Axioms -/

/--
The class of [rational numbers](https://en.wikipedia.org/wiki/Rational_number).

Provides fundamental operations and properties that any type implementing the
rational numbers must have.
-/
class Rational (ℚ : Type) extends Rational.Equivalence ℚ :=
  /-- Addition of rational numbers. -/
  addOp : Add ℚ

  /-- Multiplication of rational numbers. -/
  mulOp : Mul ℚ

  /-- Negation of rational numbers. -/
  negOp : Neg ℚ

end Lean4Axiomatic
