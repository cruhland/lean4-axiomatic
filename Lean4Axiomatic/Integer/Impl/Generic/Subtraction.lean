import Lean4Axiomatic.Integer.Subtraction

/-! # Generic implementation of integer subtraction and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Negation (ℕ := ℕ) ℤ]

/-- Define subtraction of a value from another as adding its negation. -/
def sub (a b : ℤ) : ℤ := a + (-b)

def subOp : Sub ℤ := {
  sub := sub
}

instance subtraction : Subtraction ℤ := {
  subOp := subOp
  sub_defn := Rel.refl
}

end Lean4Axiomatic.Integer.Impl.Generic
