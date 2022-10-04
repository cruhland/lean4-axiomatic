import Lean4Axiomatic.Operators

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
  eqvOp : Operators.TildeDash ℚ

attribute [instance] Rational.eqvOp

end Lean4Axiomatic.Rational
