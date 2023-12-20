import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Generic.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Induction/eliminators on formal differences -/

open Relation.Equivalence (EqvOp)

variable {ℕ : Type} [Natural ℕ]

/-- TODO -/
theorem sub_eqv_diff
    {n m : ℕ} : (n:Difference ℕ) - (m:Difference ℕ) ≃ n——m
    := calc
  _ = (n:Difference ℕ) - (m:Difference ℕ) := rfl
  _ = (n——0) - (m——0)                     := rfl
  _ ≃ (n——0) + -(m——0)                    := sub_defn
  _ = (n——0) + (0——m)                     := rfl
  _ = (n + 0)——(0 + m)                    := rfl
  _ ≃ n——(0 + m)                          := diff_substL AA.identR
  _ ≃ n——m                                := diff_substR AA.identL

/-- TODO -/
def ind_diff
    {motive : Difference ℕ → Sort u}
    {motive_eqv : {a : Difference ℕ} → EqvOp (motive a)}
    (on_diff : (n m : ℕ) → motive (n - m))
    [Induction.Constraints @motive_eqv on_diff] : (a : Difference ℕ) → motive a
    := by
  intro (n——m)
  show motive (n——m)
  have : motive (n - m) := on_diff n m
  have : motive (n——m) := motive_subst on_diff sub_eqv_diff this
  exact this

local instance ind_ops : Induction.Ops (Difference ℕ) := {
  ind_diff := ind_diff
}

/-- TODO -/
theorem ind_diff_subst
    {motive : Difference ℕ → Sort u}
    {motive_eqv : {a : Difference ℕ} → EqvOp (motive a)}
    {on_diff : (n m : ℕ) → motive (n - m)}
    [Induction.Constraints @motive_eqv on_diff]
    {a₁ a₂ : Difference ℕ} (a_eqv : a₁ ≃ a₂) :
    motive_subst on_diff ‹a₁ ≃ a₂› (ind_diff on_diff a₁) ≃ ind_diff on_diff a₂
    := by
  revert a₁ a₂; intro (n₁——m₁) (n₂——m₂) (_ : n₁——m₁ ≃ n₂——m₂)
  let a₁ := n₁——m₁; let a₂ := n₂——m₂
  let od₁ := on_diff n₁ m₁; let od₂ := on_diff n₂ m₂
  let idod := ind_diff on_diff
  show motive_subst on_diff ‹a₁ ≃ a₂› (idod a₁) ≃ idod a₂
  have diff_eqv : (n₂:Difference ℕ) - m₂ ≃ n₁ - m₁ := calc
    _ = (n₂:Difference ℕ) - m₂ := rfl
    _ ≃ n₂——m₂                 := sub_eqv_diff
    _ ≃ n₁——m₁                 := Rel.symm ‹n₁——m₁ ≃ n₂——m₂›
    _ ≃ n₁ - m₁                := Rel.symm sub_eqv_diff
  calc
    _ = motive_subst on_diff ‹a₁ ≃ a₂› (idod a₁)
      := rfl
    _ = motive_subst on_diff ‹a₁ ≃ a₂› (motive_subst on_diff sub_eqv_diff od₁)
      := rfl
    _ ≃ motive_subst on_diff (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›) od₁
      := motive_subst_compose
    _ ≃ motive_subst on_diff (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›) (motive_subst on_diff diff_eqv od₂)
      := Rel.symm (motive_subst_substR (on_diff_subst diff_eqv))
    _ ≃ motive_subst on_diff (Rel.trans diff_eqv (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›)) od₂
      := motive_subst_compose
    _ = motive_subst on_diff sub_eqv_diff od₂
      := rfl
    _ = idod a₂
      := rfl

/-- TODO -/
theorem ind_diff_eval
    {motive : Difference ℕ → Sort u}
    {motive_eqv : {a : Difference ℕ} → EqvOp (motive a)}
    {on_diff : (k j : ℕ) → motive (k - j)}
    [Induction.Constraints @motive_eqv on_diff] {n m : ℕ} :
    ind_diff on_diff (n - m) ≃ on_diff n m
    := by
  calc
    _ = ind_diff on_diff (n - m)
        := rfl
    _ ≃ motive_subst on_diff (Rel.symm sub_eqv_diff) (ind_diff on_diff (n——m))
        := Rel.symm (ind_diff_subst (Rel.symm sub_eqv_diff))
    _ = motive_subst on_diff (Rel.symm sub_eqv_diff) (motive_subst on_diff sub_eqv_diff (on_diff n m))
        := rfl
    _ ≃ motive_subst on_diff (Rel.trans sub_eqv_diff (Rel.symm sub_eqv_diff)) (on_diff n m)
        := motive_subst_compose
    _ = motive_subst on_diff Rel.refl (on_diff n m)
        := rfl
    _ ≃ on_diff n m
        := motive_subst_refl

-- TODO: This can't be proved here. Must be provided by the motive implementor
theorem motive_subst_const
    {X : Type u} [EqvOp X] {on_diff : ℕ → ℕ → X}
    [Induction.Constraints (ℤ := Difference ℕ) (λ {_} => ‹EqvOp X›) on_diff]
    {a₁ a₂ : Difference ℕ} (a_eqv : a₁ ≃ a₂) (x : X) :
    motive_subst (motive := λ _ => X) on_diff ‹a₁ ≃ a₂› x ≃ x
    := by
  admit

def ind_props : Induction.Props (Difference ℕ) := {
  ind_diff_subst := ind_diff_subst
  ind_diff_eval := ind_diff_eval
  motive_subst_const := motive_subst_const -- TODO: Move to separate typeclass
}

instance induction : Induction (Difference ℕ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Integer.Impl.Difference
