import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Generic.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Induction/eliminators on formal differences -/

variable {ℕ : Type} [Natural ℕ]

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

/-- TODO -/
theorem ind_diff_eval
    {motive : Difference ℕ → Sort u} [AA.Substitutive₁ motive (· ≃ ·) (· → ·)]
    {n m : ℕ}
    {on_diff : (k j : ℕ) → motive ((k:Difference ℕ) - (j:Difference ℕ))} :
    ind_diff on_diff ((n:Difference ℕ) - (m:Difference ℕ)) = on_diff n m
    := calc
  _ = ind_diff on_diff ((n:Difference ℕ) - (m:Difference ℕ)) := rfl
  _ = ind_diff on_diff ((n——0) - (m——0)) := rfl
  _ = ind_diff on_diff ((n——0) + -(m——0)) := rfl
  _ = ind_diff on_diff ((n——0) + (0——m)) := rfl
  _ = ind_diff on_diff ((n + 0)——(0 + m)) := rfl
  -- Here's the problem: n + 0 is not definitionally equal to n
  -- And/or, 0 + m is not definitionally equal to m
  -- Since ℕ is an abstract type, it only supports equivalence, not equality
  -- So for this argument to work, we need to use ≃ at some point
  -- And also, we need to show that ind_diff on_diff is substitutive, i.e.
  -- {a₁ a₂ : Difference ℕ} → a₁ ≃ a₂ → ind_diff on_diff a₁ ≃ ind_diff on_diff a₂

def ind_props : Induction.Props (Difference ℕ) := {
  ind_diff_eval := ind_diff_eval
}

instance induction : Induction (Difference ℕ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Integer.Impl.Difference
