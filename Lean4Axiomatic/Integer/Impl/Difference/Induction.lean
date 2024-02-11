import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Generic.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Induction/eliminators on formal differences -/

open scoped Integer.Impl.Generic
open Relation.Equivalence (
  EqvOp IndexedFamily fsubst fsubst_refl fsubst_substR fsubst_trans
)

variable {ℕ : Type} [Natural ℕ]

/-- TODO -/
theorem sub_eqv_diff
    {n m : ℕ} : (n:Difference ℕ) - m ≃ n——m
    := calc
  _ = (n:Difference ℕ) - m := rfl
  _ = (n——0) - (m——0)      := rfl
  _ ≃ (n——0) + -(m——0)     := sub_defn
  _ = (n——0) + (0——m)      := rfl
  _ = (n + 0)——(0 + m)     := rfl
  _ ≃ n——(0 + m)           := diff_substL AA.identR
  _ ≃ n——m                 := diff_substR AA.identL

/-- TODO -/
def ind_diff
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive)
    : (a : Difference ℕ) → motive a
    := by
  intro (n——m)
  show motive (n——m)
  -- TODO: `ind_diff` only needs `on_diff` from `Context` -- maybe `Ctx.Ops`?
  have : motive (n - m) := ctx.on_diff n m
  have : motive (n——m) := fsubst sub_eqv_diff this
  exact this

local instance ind_ops : Induction.Ops (Difference ℕ) := {
  ind_diff := ind_diff
}

/-- TODO -/
theorem ind_diff_subst
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive) {a₁ a₂ : Difference ℕ} (a_eqv : a₁ ≃ a₂)
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂
    := by
  revert a₁ a₂; intro (n₁——m₁) (n₂——m₂) (_ : n₁——m₁ ≃ n₂——m₂)
  let a₁ := n₁——m₁; let a₂ := n₂——m₂
  let od₁ := ctx.on_diff n₁ m₁; let od₂ := ctx.on_diff n₂ m₂
  show fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂
  have diff_eqv : (n₂:Difference ℕ) - m₂ ≃ n₁ - m₁ := calc
    _ = (n₂:Difference ℕ) - m₂ := rfl
    _ ≃ n₂——m₂                 := sub_eqv_diff
    _ ≃ n₁——m₁                 := Rel.symm ‹n₁——m₁ ≃ n₂——m₂›
    _ ≃ n₁ - m₁                := Rel.symm sub_eqv_diff
  calc
    _ = fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁)
      := rfl
    _ = fsubst ‹a₁ ≃ a₂› (fsubst sub_eqv_diff od₁)
      := rfl
    _ ≃ fsubst (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›) od₁
      := fsubst_trans
    _ ≃ fsubst (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›) (fsubst diff_eqv od₂)
    -- TODO: Needs `on_diff` and `on_diff_subst` from `Context`
      := fsubst_substR (Rel.symm ctx.on_diff_subst)
    _ ≃ fsubst (Rel.trans diff_eqv (Rel.trans sub_eqv_diff ‹a₁ ≃ a₂›)) od₂
      := fsubst_trans
    _ = fsubst (sub_eqv_diff (ℕ := ℕ)) od₂
      := rfl
    _ = ctx.ind_diff a₂
      := rfl

/-- TODO -/
theorem ind_diff_eval
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive) {n m : ℕ}
    : ctx.ind_diff (n - m) ≃ ctx.on_diff n m
    := by
  calc
    _ = ctx.ind_diff (n - m)
        := rfl
    _ ≃ fsubst (Rel.symm sub_eqv_diff) (ctx.ind_diff (n——m))
    -- TODO: Needs `ind_diff_subst`, so needs all of `Context`
        := Rel.symm (ind_diff_subst ctx (Rel.symm sub_eqv_diff))
    _ = fsubst (Rel.symm (sub_eqv_diff (ℕ := ℕ))) (fsubst sub_eqv_diff (ctx.on_diff n m))
        := rfl
    _ ≃ fsubst (Rel.trans sub_eqv_diff (Rel.symm sub_eqv_diff)) (ctx.on_diff n m)
        := fsubst_trans
    _ = fsubst Rel.refl (ctx.on_diff n m)
        := rfl
    _ ≃ ctx.on_diff n m
        := fsubst_refl

def ind_props : Induction.Props (Difference ℕ) := {
  ind_diff_subst := ind_diff_subst
  ind_diff_eval := ind_diff_eval
}

instance induction : Induction (Difference ℕ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Integer.Impl.Difference
