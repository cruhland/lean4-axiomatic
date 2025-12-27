import Lean4Axiomatic.Natural

namespace Lean4Axiomatic

open Natural (step)
open Relation.Equivalence (EqvOp)

/-! # Sequences -/

/-! ## Axioms / Definitions -/

/-- An infinite, ordered collection of the provided `Sort`'s values. -/
structure Sequence (α : Sort u) [EqvOp α] where
  /-
  Using this basic definition until there's a need for a more general one.
  The natural numbers are an infinite, ordered collection; mapping them to
  values of the given `Sort` transfers those properties.
  -/
  _at {ℕ : Type} [Natural ℕ] (index : ℕ) : α

  subst_index {ℕ : Type} [Natural ℕ] {n₁ n₂ : ℕ} : n₁ ≃ n₂ → _at n₁ ≃ _at n₂

variable {ℕ : Type} [Natural ℕ]

/-- Enable indexing notation for sequences. -/
instance seq_getElem_inst
    {α : Type u} [EqvOp α]
    : GetElem
        (coll := Sequence α) (idx := ℕ) (elem := α) (valid := λ _ _ => True)
    := {
  getElem s n _ := s._at n
}

@[gcongr]
theorem at_substR
    {α : Type u} [EqvOp α] {s : Sequence α} {n₁ n₂ : ℕ}
    : n₁ ≃ n₂ → s[n₁] ≃ s[n₂]
    := by
  intro (_ : n₁ ≃ n₂)
  show s[n₁] ≃ s[n₂]
  exact s.subst_index ‹n₁ ≃ n₂›

/-- When each value in a sequence is less than the one preceding it. -/
def InfiniteDescent {α : Type u} [EqvOp α] [LT α] (s : Sequence α) : Prop :=
  {ℕ : Type} → [Natural ℕ] → (n : ℕ) → s[n] > s[n + 1]

/-! ## Derived properties -/

/-- No natural number sequence is in infinite descent. -/
theorem inf_desc_impossible {s : Sequence ℕ} : ¬InfiniteDescent s := by
  intro (_ : InfiniteDescent s)
  have desc_at (n : ℕ) : s[n] > s[n + 1] := ‹InfiniteDescent s› n
  show False

  have : s[0] ≤ s[1] :=
    have lower_bound_at_index : (k n : ℕ) → s[n] ≥ k := by
      apply Natural.ind
      case zero =>
        intro (n : ℕ)
        show s[n] ≥ 0
        exact Natural.ge_zero
      case step =>
        intro (m : ℕ) (ih : (n : ℕ) → s[n] ≥ m) (n : ℕ)
        show s[n] ≥ step m
        have : s[n] > m := calc
          _ = s[n]     := rfl
          _ > s[n + 1] := desc_at n
          _ ≥ m        := ih (n + 1)
        have : s[n] ≥ step m := Natural.lt_step_le.mp ‹s[n] > m›
        exact this
    show s[0] ≤ s[1] from lower_bound_at_index s[0] 1

  have : s[0] > s[1] := calc
    _ = s[0]     := rfl
    _ > s[0 + 1] := desc_at 0
    _ ≃ s[1]     := by srw [Natural.zero_add]

  have : False := Natural.le_gt_false ‹s[0] ≤ s[1]› ‹s[0] > s[1]›
  exact this

end Lean4Axiomatic
