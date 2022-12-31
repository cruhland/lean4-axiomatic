
/-! # Rational numbers: addition -/

namespace Lean4Axiomatic.Rational

/-- Operations pertaining to rational number addition. -/
class Addition.Ops (ℚ : Type) :=
  /-- Addition of rational numbers. -/
  add : ℚ → ℚ → ℚ

export Addition.Ops (add)

/-- Enables the use of the `· + ·` operator for addition. -/
instance add_op_inst {ℚ : Type} [Addition.Ops ℚ] : Add ℚ := {
  add := add
}

/-- All axioms of addition for rational numbers. -/
class Addition (ℚ : Type) extends Addition.Ops ℚ

end Lean4Axiomatic.Rational
