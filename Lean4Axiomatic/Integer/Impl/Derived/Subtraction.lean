import Lean4Axiomatic.Integer.Negation
import Lean4Axiomatic.Integer.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Derived

/-! # Subtraction derived from addition and negation -/

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Equality ℤ]
variable [Conversion ℕ ℤ]
variable [Addition.Base ℕ ℤ]
variable [Negation.Base ℕ ℤ]

/-- Define subtraction of a value from another as adding its negation. -/
def sub (a b : ℤ) : ℤ := a + (-b)

instance subOp : Sub ℤ := {
  sub := sub (ℕ := ℕ)
}

instance subtraction : Subtraction.Base ℤ := {
  subOp := subOp (ℕ := ℕ)
}

end Lean4Axiomatic.Integer.Impl.Derived
