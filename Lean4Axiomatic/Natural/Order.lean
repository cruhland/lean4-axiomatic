import Lean4Axiomatic.Natural.Addition

namespace ℕ

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
  le_subst_step : AA.Substitutive (α := ℕ) step (· ≤ ·) (· ≤ ·)
  le_inject_step : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·)
  le_subst_eqv : AA.Substitutive₂ (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·)
  le_refl : Relation.Refl (α := ℕ) (· ≤ ·)
  le_trans : Relation.Trans (α := ℕ) (· ≤ ·)
  le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m
  le_subst_add : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·)
  le_cancel_add : AA.Cancellative₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·)
  le_from_eqv {n m : ℕ} : n ≃ m → n ≤ m
  le_from_lt {n m : ℕ} : n < m → n ≤ m
  le_split {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m

  lt_subst_eqv : AA.Substitutive₂ (α := ℕ) (· < ·) (· ≃ ·) (· → ·)
  lt_trans : Relation.Trans (α := ℕ) (· < ·)
  lt_zero {n : ℕ} : n ≮ 0
  lt_step {n : ℕ} : n < step n
  lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m
  lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m
  trichotomy {n m : ℕ} : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)

attribute [instance] Order.Derived.le_subst_eqv

end ℕ
