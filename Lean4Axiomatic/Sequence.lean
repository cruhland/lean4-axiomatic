import Lean4Axiomatic.Natural

namespace Lean4Axiomatic

open Natural (step)
open Relation.Equivalence (EqvOp)

/-! # Sequences -/

/-! ## Axioms / Definitions -/

/-- An infinite, ordered collection of the provided `Sort`'s values. -/
structure Sequence (α : Sort u) where
  /--
  The element identified by the provided index value.

  Using this basic definition until there's a need for a more general one. It
  works well because the natural numbers are infinite and ordered, so assigning
  an element to each of them gives us the properties we want for a sequence.
  -/
  _at {ℕ : Type} [Natural ℕ] (index : ℕ) : α

  /-- Equivalent index values produce equivalent elements. -/
  subst_index
    {ℕ : Type} [Natural ℕ] [EqvOp α] {n₁ n₂ : ℕ} : n₁ ≃ n₂ → _at n₁ ≃ _at n₂

namespace Sequence

variable {ℕ : Type} [Natural ℕ]

/-- Enable indexing notation for sequences. -/
instance seq_getElem_inst
    {α : Type u}
    : GetElem
        (coll := Sequence α) (idx := ℕ) (elem := α) (valid := λ _ _ => True)
    := {
  getElem s n _ := s._at n
}

/--
Equivalent index values produce equivalent elements.

Corollary of `subst_index` that uses indexing syntax, for use with `gcongr`.
-/
@[gcongr]
theorem at_substR
    {α : Type u} [EqvOp α] {s : Sequence α} {n₁ n₂ : ℕ}
    : n₁ ≃ n₂ → s[n₁] ≃ s[n₂]
    := by
  intro (_ : n₁ ≃ n₂)
  show s[n₁] ≃ s[n₂]
  exact s.subst_index ‹n₁ ≃ n₂›

/-- When each value in a sequence is less than the one preceding it. -/
def InfiniteDescent {α : Type u} [LT α] (s : Sequence α) : Prop :=
  {ℕ : Type} → [Natural ℕ] → (n : ℕ) → s[n] > s[step n]

/-! ## Derived properties -/

def iterate {α : Sort u} (init : α) (next : α → α) : Sequence α :=
  let nth {ℕ : Type} [Natural ℕ] (n : ℕ) : α := sorry

  have subst_index
      {ℕ : Type} [Natural ℕ] [EqvOp α] {n₁ n₂ : ℕ} : n₁ ≃ n₂ → nth n₁ ≃ nth n₂
      := by
    intro (_ : n₁ ≃ n₂)
    show nth n₁ ≃ nth n₂
    admit

  show Sequence α from {
    _at := nth
    subst_index := subst_index
  }

def iterateProp
    {α : Type u} {P : α → α → Prop} (init : α) (next : α → α)
    : ((x : α) → P x (next x)) →
      { s : Sequence α //
        {ℕ : Type} → [Natural ℕ] → (n : ℕ) → P s[n] s[step n] }
    :=
  sorry

theorem iterate_at_zero
    {α : Type u} [EqvOp α] {init : α} {next : α → α}
    : (iterate init next)[0] ≃ init
    := sorry

theorem iterate_at_step
    {α : Type u} [EqvOp α] {init : α} {next : α → α} {n : ℕ}
    : (iterate init next)[step n] ≃ next (iterate init next)[n]
    := sorry

theorem iterate_chain
    {α : Type u} [EqvOp α]
    {P : α → α → Prop} [AA.Substitutive₂ P AA.tc (· ≃ ·) (· → ·)]
    {init : α} {next : α → α} [AA.Substitutive₁ next (· ≃ ·) (· ≃ ·)]
    (P_link : (x : α) → P x (next x))
    : let s := iterate init next
      (n : ℕ) → P s[n] s[step n]
    := by
  intro (s : Sequence α)
  apply Natural.ind
  case zero =>
    show P s[0] s[step 0]
    have : P init (next init) := P_link init
    have : P (iterate init next)[0] (next init) :=
      AA.substLFn (Rel.symm iterate_at_zero) ‹P init (next init)›
    have : P s[0] (next init) := this
    have : P s[0] (next (iterate init next)[0]) :=
      AA.substRFn (AA.subst₁ (Rel.symm iterate_at_zero)) ‹P s[0] (next init)›
    have : P s[0] (iterate init next)[step 0] :=
      AA.substRFn (Rel.symm iterate_at_step) this
    have : P s[0] s[step 0] := this
    exact this
  case step =>
    intro (m : ℕ) (ih : P s[m] s[step m])
    show P s[step m] s[step (step m)]
    have : P s[step m] (next s[step m]) := P_link s[step m]
    have : P s[step m] (next (iterate init next)[step m]) := this
    have : P s[step m] (iterate init next)[step (step m)] :=
      AA.substRFn (Rel.symm iterate_at_step) this
    have : P s[step m] s[step (step m)] := this
    exact this

/-
Sequence Elem map (f : Elem → ℕ) → Sequence ℕ
P := λ e ne => e.val.1 > ne.val.1
P' := λ x nx => x > nx
f := λ e => e.val.1

let s := iterate init next
let P' := λ x nx => P (f x) (f nx)
(n : ℕ) → P' s[n] s[n + 1]
let s' := map f s
(n : ℕ) → P s'[n] s'[n + 1]
-/

/-- No natural number sequence is in infinite descent. -/
theorem inf_desc_impossible {s : Sequence ℕ} : ¬InfiniteDescent s := by
  intro (_ : InfiniteDescent s)
  have desc_at (n : ℕ) : s[n] > s[step n] := ‹InfiniteDescent s› n
  show False

  have : s[0] > s[1] := calc
    _ = s[0]      := rfl
    _ > s[step 0] := desc_at 0
    _ ≃ s[1]      := by srw [←Natural.literal_step]

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
          _ = s[n]      := rfl
          _ > s[step n] := desc_at n
          _ ≥ m         := ih (step n)
        have : s[n] ≥ step m := Natural.lt_step_le.mp ‹s[n] > m›
        exact this
    show s[0] ≤ s[1] from lower_bound_at_index s[0] 1

  have : False := Natural.le_gt_false ‹s[0] ≤ s[1]› ‹s[0] > s[1]›
  exact this

end Lean4Axiomatic.Sequence
