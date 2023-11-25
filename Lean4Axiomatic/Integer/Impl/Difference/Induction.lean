import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Generic.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Induction/eliminators on formal differences -/

open Relation.Equivalence (EqvOp)

variable {ℕ : Type} [Natural ℕ]

/-- TODO -/
theorem sub_eqv_diff
    {n m : ℕ} : (n:Difference ℕ) - (m:Difference ℕ) ≃ n——m
    :=
  sorry

/-- TODO -/
def ind_diff
    {motive : Difference ℕ → Sort u} [AA.Substitutive₁ motive (· ≃ ·) (· → ·)]
    (on_diff : (n m : ℕ) → motive (n - m)) : (a : Difference ℕ) → motive a
    := by
  intro (n——m)
  show motive (n——m)
  have : motive (n - m) := on_diff n m
  have : motive (n——m) := AA.substFn sub_eqv_diff this
  exact this

local instance ind_ops : Induction.Ops (Difference ℕ) := {
  ind_diff := ind_diff
}

-- TODO: Signatures for substFn_substL and substFn_substR

/-- TODO -/
theorem substFn_compose
    {α : Sort u} {f : α → Sort v} [EqvOp α] (f_eqv : {x : α} → EqvOp (f x))
    [AA.Substitutive₁ f (· ≃ ·) (· → ·)]
    {x y z : α} {eqv₁ : x ≃ y} {eqv₂ : y ≃ z} {fx : f x} :
    AA.substFn eqv₂ (AA.substFn eqv₁ fx) ≃ AA.substFn (Rel.trans eqv₁ eqv₂) fx
    := by
  admit

/-- TODO -/
theorem ind_diff_subst_diff
    {motive : Difference ℕ → Sort u} [AA.Substitutive₁ motive (· ≃ ·) (· → ·)]
    (motive_eqv : {a : Difference ℕ} → EqvOp (motive a))
    {on_diff : (n m : ℕ) → motive (n - m)}
    (on_diff_subst : {k₁ j₁ k₂ j₂ : ℕ} → (diff_eqv : (k₁:Difference ℕ) - j₁ ≃ k₂ - j₂) → AA.substFn diff_eqv (on_diff k₁ j₁) ≃ on_diff k₂ j₂)
    {a₁ a₂ : Difference ℕ} (a_eqv : a₁ ≃ a₂) :
    AA.substFn ‹a₁ ≃ a₂› (ind_diff on_diff a₁) ≃ ind_diff on_diff a₂
    := by
  revert a₁ a₂; intro (n₁——m₁) (n₂——m₂) (_ : n₁——m₁ ≃ n₂——m₂)
  let a₁ := n₁——m₁; let a₂ := n₂——m₂
  let od₁ := on_diff n₁ m₁; let od₂ := on_diff n₂ m₂
  let idod := ind_diff on_diff
  show AA.substFn ‹a₁ ≃ a₂› (idod a₁) ≃ idod a₂
  have : (n₂:Difference ℕ) - m₂ ≃ n₁ - m₁ := sorry
  calc
    _ = AA.substFn ‹a₁ ≃ a₂› (idod a₁)
      := rfl
    _ = AA.substFn ‹a₁ ≃ a₂› (AA.substFn sub_eqv_diff od₁)
      := rfl
    _ ≃ AA.substFn (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›) od₁
      := substFn_compose motive_eqv
    _ ≃ AA.substFn (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›) (AA.substFn ‹(n₂:Difference ℕ) - m₂ ≃ n₁ - m₁› od₂)
      := sorry -- substFn_substR
    _ ≃ AA.substFn (Rel.trans ‹(n₂:Difference ℕ) - m₂ ≃ n₁ - m₁› (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›)) od₂
      := sorry -- substFn_compose
    _ ≃ AA.substFn sub_eqv_diff od₂
      := sorry -- substFn_substL
    _ = idod a₂
      := rfl

    -- substFn ‹n₁ - m₁ ≃ n₁——m₁ ≃ n₂——m₂› (on_diff n₁ m₁ : motive (n₁ - m₁)) : motive (n₂——m₂)
    -- need something that shows n₁ + m₂ ≃ n₂ + m₁ → on_diff n₁ m₁ : motive (n₁ - m₁) ≃ substFn ‹n₁ - m₁ ≃ n₂ - m₂› on_diff n₂ m₂ : motive (n₂ - m₂)
    -- we want a substFn_subst
    -- if we have fx₁ ≃ substFn eqv₂ fx₂
    -- then we can conclude substFn eqv₁ fx₁ ≃ substFn eqv₁ (substFn eqv₂ fx₂)
    -- and then eqv₁ and eqv₂ can be combined to collapse the substFn levels
    -- then need substFn ‹y ≃ z› (fy : f y) ≃ substFn ‹x ≃ z› (fx : f x)
    -- substFn ‹n₂ - m₂ ≃ n₂——m₂› (on_diff n₂ m₂ : motive (n₂ - m₂)) : motive (n₂——m₂)

/-- TODO -/
theorem substFn_symm_cancel
    {α : Sort u} [EqvOp α] {β : α → Sort v} (β_eqv : {a : α} → EqvOp (β a))
    [AA.Substitutive₁ β (· ≃ ·) (· → ·)] {a₁ a₂ : α} {eqv : a₁ ≃ a₂}
    {b : β a₁} : AA.substFn (Rel.symm eqv) (AA.substFn eqv b) ≃ b
    := by
  admit

/-- TODO -/
theorem ind_diff_eval
    {motive : Difference ℕ → Sort u} [AA.Substitutive₁ motive (· ≃ ·) (· → ·)]
    (motive_eqv : {a : Difference ℕ} → EqvOp (motive a)) {n m : ℕ}
    {on_diff : (k j : ℕ) → motive ((k:Difference ℕ) - (j:Difference ℕ))} :
    ind_diff on_diff ((n:Difference ℕ) - (m:Difference ℕ)) ≃ on_diff n m
    := calc
  _ = ind_diff on_diff ((n:Difference ℕ) - (m:Difference ℕ))
      := rfl
  _ ≃ AA.substFn (Rel.symm sub_eqv_diff) (ind_diff on_diff (n——m))
      := Rel.symm (ind_diff_subst_diff motive_eqv (Rel.symm sub_eqv_diff))
  _ = AA.substFn (Rel.symm sub_eqv_diff) (AA.substFn sub_eqv_diff (on_diff n m))
      := rfl
  _ ≃ on_diff n m
      := substFn_symm_cancel (β := motive) motive_eqv

def ind_props : Induction.Props (Difference ℕ) := {
  ind_diff_eval := ind_diff_eval -- TODO: Fix signature in axioms
}

instance induction : Induction (Difference ℕ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Integer.Impl.Difference
