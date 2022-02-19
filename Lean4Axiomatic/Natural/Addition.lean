import Lean4Axiomatic.Natural.Core

namespace Lean4Axiomatic
namespace Natural

class Addition.Base (ℕ : Type) [Core ℕ] where
  addOp : Add ℕ

  zero_add {m : ℕ} : 0 + m ≃ m
  step_add {n m : ℕ} : step n + m ≃ step (n + m)

attribute [instance] Addition.Base.addOp

class Addition.Derived (ℕ : Type) [Core ℕ] extends Addition.Base ℕ where
  add_zero {n : ℕ} : n + 0 ≃ n
  add_step {n m : ℕ} : n + step m ≃ step (n + m)
  add_substitutive : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·)
  add_one_step {n : ℕ} : n + 1 ≃ step n
  add_commutative : AA.Commutative (α := ℕ) (· + ·)
  add_assoc {n m k : ℕ} : (n + m) + k ≃ n + (m + k)
  cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k
  zero_sum_split {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0

attribute [instance] Addition.Derived.add_commutative
attribute [instance] Addition.Derived.add_substitutive

namespace Addition
export Addition.Base (addOp step_add zero_add)
export Addition.Derived (
  add_assoc add_commutative add_one_step add_step add_substitutive add_zero cancel_add
  zero_sum_split
)
end Addition

export Addition (
  add_assoc add_commutative add_one_step addOp add_step add_substitutive
  add_zero cancel_add step_add zero_add zero_sum_split
)

end Natural
end Lean4Axiomatic
