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
  have : motive (n - m) := ctx.on_diff n m
  have : motive (n——m) := fsubst sub_eqv_diff this
  exact this

local instance ind_ops : Induction.Ops (Difference ℕ) := {
  ind_diff := ind_diff
}

/-- TODO -/
theorem ind_diff_subst
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    {ctx : Induction.Context motive} {a₁ a₂ : Difference ℕ} {a_eqv : a₁ ≃ a₂}
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂
    := by
  revert a₁ a₂; intro (n₁——m₁) (n₂——m₂)
  let a₁ := n₁——m₁; let a₂ := n₂——m₂
  intro (_ : a₁ ≃ a₂)
  show fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂

  let d₁ := (n₁:Difference ℕ) - m₁; let d₂ := (n₂:Difference ℕ) - m₂
  have : d₁ ≃ a₁ := sub_eqv_diff
  have : d₂ ≃ a₂ := sub_eqv_diff
  have : d₁ ≃ a₂ := Rel.trans ‹d₁ ≃ a₁› ‹a₁ ≃ a₂›
  have : d₂ ≃ d₁ := Rel.trans ‹d₂ ≃ a₂› (Rel.symm ‹d₁ ≃ a₂›)

  let od₁ := ctx.on_diff n₁ m₁; let od₂ := ctx.on_diff n₂ m₂
  have od_subst : od₁ ≃ fsubst ‹d₂ ≃ d₁› od₂ := Rel.symm ctx.on_diff_subst
  calc
    _ = fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁)         := rfl
    _ = fsubst ‹a₁ ≃ a₂› (fsubst ‹d₁ ≃ a₁› od₁)    := rfl
    _ ≃ fsubst (Rel.trans ‹d₁ ≃ a₁› ‹a₁ ≃ a₂›) od₁ := fsubst_trans
    _ = fsubst ‹d₁ ≃ a₂› od₁                       := rfl
    _ ≃ fsubst ‹d₁ ≃ a₂› (fsubst ‹d₂ ≃ d₁› od₂)    := fsubst_substR od_subst
    _ ≃ fsubst (Rel.trans ‹d₂ ≃ d₁› ‹d₁ ≃ a₂›) od₂ := fsubst_trans
    _ = fsubst ‹d₂ ≃ a₂› od₂                       := rfl
    _ = ctx.ind_diff a₂                            := rfl

/-- TODO -/
theorem ind_diff_eval
    {motive : Difference ℕ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive) {n m : ℕ}
    : ctx.ind_diff (n - m) ≃ ctx.on_diff n m
    := by
  have sed : (n:Difference ℕ) - m ≃ n——m := sub_eqv_diff
  have des : n——m ≃ n - m := Rel.symm sed
  calc
    _ = ctx.ind_diff (n - m)                         := rfl
    _ ≃ fsubst des (ctx.ind_diff (n——m))             := Rel.symm ind_diff_subst
    _ = fsubst des (fsubst sed (ctx.on_diff n m))    := rfl
    _ ≃ fsubst (Rel.trans sed des) (ctx.on_diff n m) := fsubst_trans
    _ = fsubst Rel.refl (ctx.on_diff n m)            := rfl
    _ ≃ ctx.on_diff n m                              := fsubst_refl

def ind_props : Induction.Props (Difference ℕ) := {
  ind_diff_subst := ind_diff_subst
  ind_diff_eval := ind_diff_eval
}

instance induction : Induction (Difference ℕ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Integer.Impl.Difference
