import Lean4Axiomatic.Relation.Equivalence

/-! # Rational numbers -/

namespace Lean4Axiomatic.Rational

/-! ## Axioms -/

/--
The class of [rational numbers](https://en.wikipedia.org/wiki/Rational_number).

Provides fundamental operations and properties that any type implementing the
rational numbers must have.
-/
class Rational (ℚ : Type) :=
  /-- Equivalence of rational numbers. -/
  eqvOp : Relation.Equivalence.EqvOp ℚ

  /-- Addition of rational numbers. -/
  addOp : Add ℚ

  /-- Multiplication of rational numbers. -/
  mulOp : Mul ℚ

  /-- Negation of rational numbers. -/
  negOp : Neg ℚ

attribute [instance] Rational.eqvOp

end Lean4Axiomatic.Rational
