import Lean4Axiomatic.Natural.Order

namespace Lean4Axiomatic
namespace Natural

variable {ℕ : Type}
variable [Core ℕ]
variable [Addition.Base ℕ]

instance : LE ℕ := LE.mk λ n m => ∃ k : ℕ, n + k ≃ m
instance : LT ℕ := LT.mk λ n m => n ≤ m ∧ n ≄ m

instance order_base : Order.Base ℕ where
  leOp := inferInstance
  le_defn {n m : ℕ} := Iff.intro id id

  ltOp := inferInstance
  lt_defn {n m : ℕ} := Iff.intro id id

end Natural
end Lean4Axiomatic
