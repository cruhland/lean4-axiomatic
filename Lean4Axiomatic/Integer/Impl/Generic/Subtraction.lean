import Lean4Axiomatic.Integer.Subtraction

/-! # Generic implementation of integer subtraction and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Negation (ℕ := ℕ) ℤ]

/-- Define subtraction of a value from another as adding its negation. -/
def sub (a b : ℤ) : ℤ := a + (-b)

local instance sub_ops : Subtraction.Ops ℤ := {
  sub := sub
}

theorem sub_defn {a b : ℤ} : a - b ≃ a + (-b) := Rel.refl

def sub_props : Subtraction.Props ℤ := {
  sub_defn := sub_defn
}

instance subtraction : Subtraction ℤ := {
  toOps := sub_ops
  toProps := sub_props
}

end Lean4Axiomatic.Integer.Impl.Generic
