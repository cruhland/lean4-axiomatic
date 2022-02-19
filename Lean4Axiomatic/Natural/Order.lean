import Lean4Axiomatic.Natural.Addition

namespace Lean4Axiomatic
namespace Natural

class Order.Base (ℕ : Type) [Core ℕ] [Addition.Base ℕ] where
  leOp : LE ℕ
  le_defn {n m : ℕ} : n ≤ m ↔ ∃ k : ℕ, n + k ≃ m

  ltOp : LT ℕ
  lt_defn {n m : ℕ} : n < m ↔ n ≤ m ∧ n ≄ m

-- Higher priority than the stdlib definitions
attribute [instance default+1] Order.Base.leOp
attribute [instance default+1] Order.Base.ltOp

class Order.Derived (ℕ : Type) [Core ℕ] [Addition.Base ℕ]
    extends Order.Base ℕ where
  le_substitutive_step : AA.Substitutive (α := ℕ) step (· ≤ ·) (· ≤ ·)
  le_injective_step : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·)
  le_substitutive_eqv : AA.Substitutive₂ (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·)
  le_reflexive : Relation.Refl (α := ℕ) (· ≤ ·)
  le_transitive : Relation.Trans (α := ℕ) (· ≤ ·)
  le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m
  le_substitutive_add : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·)
  le_cancellative_add : AA.Cancellative₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·)
  le_from_eqv {n m : ℕ} : n ≃ m → n ≤ m
  le_from_lt {n m : ℕ} : n < m → n ≤ m
  le_split {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m

  lt_substitutive_eqv : AA.Substitutive₂ (α := ℕ) (· < ·) (· ≃ ·) (· → ·)
  lt_transitive : Relation.Trans (α := ℕ) (· < ·)
  lt_zero {n : ℕ} : n ≮ 0
  lt_step {n : ℕ} : n < step n
  lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m
  lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m
  trichotomy {n m : ℕ} : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)

attribute [instance] Order.Derived.le_substitutive_eqv

namespace Order
export Order.Base (le_defn leOp lt_defn ltOp)
export Order.Derived (
  le_antisymm le_reflexive le_split le_transitive
  lt_split lt_step lt_step_le lt_zero trichotomy
)
end Order

export Order (
  le_antisymm le_defn le_reflexive le_split le_transitive leOp
  lt_defn ltOp lt_split lt_step lt_step_le lt_zero trichotomy
)

end Natural
end Lean4Axiomatic
