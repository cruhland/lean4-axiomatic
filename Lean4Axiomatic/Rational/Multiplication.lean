
/-! # Rational numbers: multiplication -/

namespace Lean4Axiomatic.Rational

/-- Operations pertaining to rational number multiplication. -/
class Multiplication.Ops (ℚ : Type) :=
  /-- Multiplication of rational numbers. -/
  mul : ℚ → ℚ → ℚ

export Multiplication.Ops (mul)

/-- Enables the use of the `· * ·` operator for multiplication. -/
instance mul_op_inst {ℚ : Type} [Multiplication.Ops ℚ] : Mul ℚ := {
  mul := mul
}

/-- All axioms of multiplication for rational numbers. -/
class Multiplication (ℚ : Type) extends Multiplication.Ops ℚ

end Lean4Axiomatic.Rational
