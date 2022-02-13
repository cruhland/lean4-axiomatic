import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic
namespace Natural

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms.Derived ℕ]
variable [Addition.Derived ℕ]
variable [Sign.Derived ℕ]
variable [Order.Base ℕ]

theorem le_subst_step {n₁ n₂ : ℕ} : n₁ ≤ n₂ → step n₁ ≤ step n₂ := by
  intro (_ : n₁ ≤ n₂)
  show step n₁ ≤ step n₂
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := Order.Base.le_defn.mp ‹n₁ ≤ n₂›
  apply Order.Base.le_defn.mpr
  exists d
  show step n₁ + d ≃ step n₂
  calc
    _ ≃ step n₁ + d := Eqv.refl
    _ ≃ step (n₁ + d) := Addition.step_add
    _ ≃ step n₂ := AA.subst ‹n₁ + d ≃ n₂›

instance : AA.Substitutive (α := ℕ) step (· ≤ ·) (· ≤ ·) where
  subst := le_subst_step

theorem le_inject_step {n₁ n₂ : ℕ} : step n₁ ≤ step n₂ → n₁ ≤ n₂ := by
  intro (_ : step n₁ ≤ step n₂)
  show n₁ ≤ n₂
  have ⟨d, (_ : step n₁ + d ≃ step n₂)⟩ :=
    Order.Base.le_defn.mp ‹step n₁ ≤ step n₂›
  apply Order.Base.le_defn.mpr
  exists d
  show n₁ + d ≃ n₂
  have : step (n₁ + d) ≃ step n₂ := calc
    _ ≃ step (n₁ + d) := Eqv.refl
    _ ≃ step n₁ + d := Eqv.symm Addition.step_add
    _ ≃ step n₂ := ‹step n₁ + d ≃ step n₂›
  exact AA.inject ‹step (n₁ + d) ≃ step n₂›

instance : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·) where
  inject := le_inject_step

theorem le_subst_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ ≤ m → n₂ ≤ m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ ≤ m)
  show n₂ ≤ m
  have ⟨d, (_ : n₁ + d ≃ m)⟩ := Order.Base.le_defn.mp ‹n₁ ≤ m›
  apply Order.Base.le_defn.mpr
  exists d
  show n₂ + d ≃ m
  calc
    _ ≃ n₂ + d := Eqv.refl
    _ ≃ n₁ + d := Eqv.symm (AA.substL ‹n₁ ≃ n₂›)
    _ ≃ m      := ‹n₁ + d ≃ m›

instance
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·) where
  subst₂ := le_subst_eqv

theorem le_eqv_subst {n m₁ m₂ : ℕ} : m₁ ≃ m₂ → n ≤ m₁ → n ≤ m₂ := by
  intro (_ : m₁ ≃ m₂) (_ : n ≤ m₁)
  show n ≤ m₂
  have ⟨d, (_ : n + d ≃ m₁)⟩ := Order.Base.le_defn.mp ‹n ≤ m₁›
  apply Order.Base.le_defn.mpr
  exists d
  show n + d ≃ m₂
  exact Eqv.trans ‹n + d ≃ m₁› ‹m₁ ≃ m₂›

instance
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·) where
  subst₂ := le_eqv_subst

instance : AA.Substitutive₂ (α := ℕ) (· ≤ ·) (· ≃ ·) (· → ·) :=
  AA.Substitutive₂.mk

theorem le_refl {n : ℕ} : n ≤ n := by
  apply Order.Base.le_defn.mpr
  exists (0 : ℕ)
  show n + 0 ≃ n
  exact Addition.add_zero

instance : Relation.Refl (α := ℕ) (· ≤ ·) where
  refl := le_refl

theorem le_step_split {n m : ℕ} : n ≤ step m → n ≤ m ∨ n ≃ step m := by
  intro (_ : n ≤ step m)
  show n ≤ m ∨ n ≃ step m
  have ⟨d, (_ : n + d ≃ step m)⟩ := Order.Base.le_defn.mp ‹n ≤ step m›
  let motive := λ x => d ≃ x → n ≤ m ∨ n ≃ step m
  apply (Axioms.cases_on (motive := motive) d · · Eqv.refl)
  · intro (_ : d ≃ 0)
    apply Or.inr
    show n ≃ step m
    calc
      _ ≃ n      := Eqv.refl
      _ ≃ n + 0  := Eqv.symm Addition.add_zero
      _ ≃ n + d  := Eqv.symm (AA.substR ‹d ≃ 0›)
      _ ≃ step m := ‹n + d ≃ step m›
  · intro e (_ : d ≃ step e)
    apply Or.inl
    show n ≤ m
    apply Order.Base.le_defn.mpr
    exists e
    show n + e ≃ m
    apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
    show step (n + e) ≃ step m
    calc
      _ ≃ step (n + e) := Eqv.refl
      _ ≃ n + step e   := Eqv.symm Addition.add_step
      _ ≃ n + d        := Eqv.symm (AA.substR ‹d ≃ step e›)
      _ ≃ step m       := ‹n + d ≃ step m›

theorem le_step {n m : ℕ} : n ≤ m → n ≤ step m := by
  intro (_ : n ≤ m)
  show n ≤ step m
  have ⟨d, (_ : n + d ≃ m)⟩ := Order.Base.le_defn.mp ‹n ≤ m›
  apply Order.Base.le_defn.mpr
  exists step d
  show n + step d ≃ step m
  calc
    _ ≃ n + step d   := Eqv.refl
    _ ≃ step (n + d) := Addition.add_step
    _ ≃ step m       := AA.subst ‹n + d ≃ m›

theorem le_trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k := by
  intro (_ : n ≤ m)
  have ⟨d, (_ : n + d ≃ m)⟩ := Order.Base.le_defn.mp ‹n ≤ m›
  apply Axioms.ind_on (motive := λ k => m ≤ k → n ≤ k) k
  case zero =>
    intro (_ : m ≤ 0)
    have ⟨e, (_ : m + e ≃ 0)⟩ := Order.Base.le_defn.mp ‹m ≤ 0›
    show n ≤ 0
    apply Order.Base.le_defn.mpr
    exists d + e
    show n + (d + e) ≃ 0
    calc
      _ ≃ n + (d + e) := Eqv.refl
      _ ≃ (n + d) + e := Eqv.symm Addition.add_assoc
      _ ≃ m + e       := AA.substL ‹n + d ≃ m›
      _ ≃ 0           := ‹m + e ≃ 0›
  case step =>
    intro k (ih : m ≤ k → n ≤ k) (_ : m ≤ step k)
    show n ≤ step k
    match le_step_split ‹m ≤ step k› with
    | Or.inl (_ : m ≤ k) =>
      exact le_step (ih ‹m ≤ k›)
    | Or.inr (_ : m ≃ step k) =>
      exact AA.substR (rβ := (· → ·)) ‹m ≃ step k› ‹n ≤ m›

instance : Relation.Trans (α := ℕ) (· ≤ ·) where
  trans := le_trans

theorem le_subst_add {n₁ n₂ m : ℕ} : n₁ ≤ n₂ → n₁ + m ≤ n₂ + m := by
  intro (_ : n₁ ≤ n₂)
  show n₁ + m ≤ n₂ + m
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := Order.Base.le_defn.mp ‹n₁ ≤ n₂›
  apply Order.Base.le_defn.mpr
  exists d
  show (n₁ + m) + d ≃ n₂ + m
  calc
    _ ≃ (n₁ + m) + d := Eqv.refl
    _ ≃ n₁ + (m + d) := Addition.add_assoc
    _ ≃ n₁ + (d + m) := AA.substR AA.comm
    _ ≃ (n₁ + d) + m := Eqv.symm Addition.add_assoc
    _ ≃ n₂ + m       := AA.substL ‹n₁ + d ≃ n₂›

instance
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) where
  subst₂ := le_subst_add

instance
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.substR_from_substL_swap

instance : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.Substitutive₂.mk

theorem le_cancel_add {n m₁ m₂ : ℕ} : n + m₁ ≤ n + m₂ → m₁ ≤ m₂ := by
  intro (_ : n + m₁ ≤ n + m₂)
  show m₁ ≤ m₂
  have ⟨d, (_ : (n + m₁) + d ≃ n + m₂)⟩ :=
    Order.Base.le_defn.mp ‹n + m₁ ≤ n + m₂›
  apply Order.Base.le_defn.mpr
  exists d
  show m₁ + d ≃ m₂
  have : n + (m₁ + d) ≃ n + m₂ := calc
    _ ≃ n + (m₁ + d) := Eqv.refl
    _ ≃ (n + m₁) + d := Eqv.symm Addition.add_assoc
    _ ≃ n + m₂       := ‹(n + m₁) + d ≃ n + m₂›
  exact Addition.cancel_add ‹n + (m₁ + d) ≃ n + m₂›

instance : AA.Cancellative AA.Hand.L (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) where
  cancel := le_cancel_add

instance : AA.Cancellative AA.Hand.R (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.cancelR_from_cancelL

instance : AA.Cancellative₂ (α := ℕ) (· + ·) (· ≤ ·) (· ≤ ·) :=
  AA.Cancellative₂.mk

theorem le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m := by
  intro (_ : n ≤ m) (_ : m ≤ n)
  show n ≃ m
  have ⟨d₁, (_ : n + d₁ ≃ m)⟩ := Order.Base.le_defn.mp ‹n ≤ m›
  have ⟨d₂, (_ : m + d₂ ≃ n)⟩ := Order.Base.le_defn.mp ‹m ≤ n›
  have : n + (d₁ + d₂) ≃ n + 0 := calc
    _ ≃ n + (d₁ + d₂) := Eqv.refl
    _ ≃ (n + d₁) + d₂ := Eqv.symm Addition.add_assoc
    _ ≃ m + d₂        := AA.substL ‹n + d₁ ≃ m›
    _ ≃ n             := ‹m + d₂ ≃ n›
    _ ≃ n + 0         := Eqv.symm Addition.add_zero
  have : d₁ + d₂ ≃ 0 := Addition.cancel_add ‹n + (d₁ + d₂) ≃ n + 0›
  have ⟨(_ : d₁ ≃ 0), _⟩ := Addition.zero_sum_split ‹d₁ + d₂ ≃ 0›
  calc
    _ ≃ n      := Eqv.refl
    _ ≃ n + 0  := Eqv.symm Addition.add_zero
    _ ≃ n + d₁ := Eqv.symm (AA.substR ‹d₁ ≃ 0›)
    _ ≃ m      := ‹n + d₁ ≃ m›

theorem lt_subst_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ < m → n₂ < m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ < m)
  show n₂ < m
  have ⟨(_ : n₁ ≤ m), (_ : n₁ ≄ m)⟩ := Order.Base.lt_defn.mp ‹n₁ < m›
  have : n₂ ≤ m := AA.substL (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹n₁ ≤ m›
  have : n₂ ≄ m := AA.substL (f := (· ≄ ·)) (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹n₁ ≄ m›
  apply Order.Base.lt_defn.mpr
  exact ⟨‹n₂ ≤ m›, ‹n₂ ≄ m›⟩

instance
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· < ·) (· ≃ ·) (· → ·) where
  subst₂ := lt_subst_eqv

theorem lt_eqv_subst {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m < n₁ → m < n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : m < n₁)
  show m < n₂
  have ⟨(_ : m ≤ n₁), (_ : m ≄ n₁)⟩ := Order.Base.lt_defn.mp ‹m < n₁›
  have : m ≤ n₂ := AA.substR (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹m ≤ n₁›
  have : m ≄ n₂ := AA.substR (f := (· ≄ ·)) (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹m ≄ n₁›
  apply Order.Base.lt_defn.mpr
  exact ⟨‹m ≤ n₂›, ‹m ≄ n₂›⟩

instance
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· < ·) (· ≃ ·) (· → ·) where
  subst₂ := lt_eqv_subst

instance : AA.Substitutive₂ (α := ℕ) (· < ·) (· ≃ ·) (· → ·) :=
  AA.Substitutive₂.mk

theorem lt_step {n : ℕ} : n < step n := by
  show n < step n
  apply Order.Base.lt_defn.mpr
  apply And.intro
  · show n ≤ step n
    apply Order.Base.le_defn.mpr
    exists (1 : ℕ)
    show n + 1 ≃ step n
    exact Addition.add_one_step
  · show n ≄ step n
    exact Eqv.symm Axioms.Derived.step_neq

theorem lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m := by
  apply Iff.intro
  · intro (_ : n < m)
    show step n ≤ m
    have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := Order.Base.lt_defn.mp ‹n < m›
    have ⟨d, (_ : n + d ≃ m)⟩ := Order.Base.le_defn.mp ‹n ≤ m›
    have : d ≄ 0 := by
      intro (_ : d ≃ 0)
      show False
      apply ‹n ≄ m›
      show n ≃ m
      calc
        _ ≃ n     := Eqv.refl
        _ ≃ n + 0 := Eqv.symm Addition.add_zero
        _ ≃ n + d := Eqv.symm (AA.substR ‹d ≃ 0›)
        _ ≃ m     := ‹n + d ≃ m›
    have : Positive d := Sign.positive_defn.mpr ‹d ≄ 0›
    have ⟨d', (_ : step d' ≃ d)⟩ := Sign.positive_step ‹Positive d›
    show step n ≤ m
    apply Order.Base.le_defn.mpr
    exists d'
    show step n + d' ≃ m
    calc
      _ ≃ step n + d'   := Eqv.refl
      _ ≃ step (n + d') := Addition.step_add
      _ ≃ n + step d'   := Eqv.symm Addition.add_step
      _ ≃ n + d         := AA.substR ‹step d' ≃ d›
      _ ≃ m             := ‹n + d ≃ m›
  · intro (_ : step n ≤ m)
    show n < m
    have ⟨d, (_ : step n + d ≃ m)⟩ := Order.Base.le_defn.mp ‹step n ≤ m›
    have : n + step d ≃ m := calc
      _ ≃ n + step d   := Eqv.refl
      _ ≃ step (n + d) := Addition.add_step
      _ ≃ step n + d   := Eqv.symm Addition.step_add
      _ ≃ m            := ‹step n + d ≃ m›
    have : ∃ d, n + d ≃ m := ⟨step d, ‹n + step d ≃ m›⟩
    have : n ≤ m := Order.Base.le_defn.mpr ‹∃ d, n + d ≃ m›
    have : n ≄ m := by
      intro (_ : n ≃ m)
      show False
      have : n + step d ≃ n + 0 := calc
        _ ≃ n + step d := Eqv.refl
        _ ≃ m := ‹n + step d ≃ m›
        _ ≃ n := Eqv.symm ‹n ≃ m›
        _ ≃ n + 0 := Eqv.symm Addition.add_zero
      have : step d ≃ 0 := Addition.cancel_add ‹n + step d ≃ n + 0›
      exact absurd this Axioms.step_neq_zero
    show n < m
    apply Order.Base.lt_defn.mpr
    exact ⟨‹n ≤ m›, ‹n ≄ m›⟩

theorem lt_zero {n : ℕ} : n ≮ 0 := by
  intro (_ : n < 0)
  show False
  have : step n ≤ 0 := lt_step_le.mp ‹n < 0›
  have ⟨d, (_ : step n + d ≃ 0)⟩ := Order.Base.le_defn.mp ‹step n ≤ 0›
  have : step (n + d) ≃ 0 := calc
    _ ≃ step (n + d) := Eqv.refl
    _ ≃ step n + d   := Eqv.symm Addition.step_add
    _ ≃ 0            := ‹step n + d ≃ 0›
  exact absurd ‹step (n + d) ≃ 0› Axioms.step_neq_zero

theorem le_from_eqv {n m : ℕ} : n ≃ m → n ≤ m := by
  intro (_ : n ≃ m)
  show n ≤ m
  have : n ≤ n := Eqv.refl
  exact AA.substR (rβ := (· → ·)) ‹n ≃ m› ‹n ≤ n›

theorem le_from_lt {n m : ℕ} : n < m → n ≤ m := by
  intro (_ : n < m)
  show n ≤ m
  have ⟨(_ : n ≤ m), _⟩ := Order.Base.lt_defn.mp ‹n < m›
  exact ‹n ≤ m›

theorem le_split {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m := by
  intro (_ : n ≤ m)
  show n < m ∨ n ≃ m
  have ⟨d, (h : n + d ≃ m)⟩ := Order.Base.le_defn.mp ‹n ≤ m›
  revert h
  apply Axioms.cases_on (motive := λ d => n + d ≃ m → n < m ∨ n ≃ m) d
  case zero =>
    intro (_ : n + 0 ≃ m)
    apply Or.inr
    show n ≃ m
    calc
      _ ≃ n     := Eqv.refl
      _ ≃ n + 0 := Eqv.symm Addition.add_zero
      _ ≃ m     := ‹n + 0 ≃ m›
  case step =>
    intro d (_ : n + step d ≃ m)
    apply Or.inl
    show n < m
    apply lt_step_le.mpr
    show step n ≤ m
    apply Order.Base.le_defn.mpr
    exists d
    show step n + d ≃ m
    calc
      _ ≃ step n + d   := Eqv.refl
      _ ≃ step (n + d) := Addition.step_add
      _ ≃ n + step d   := Eqv.symm Addition.add_step
      _ ≃ m            := ‹n + step d ≃ m›

theorem lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m := by
  intro (_ : n < step m)
  show n < m ∨ n ≃ m
  have : step n ≤ step m := lt_step_le.mp ‹n < step m›
  have : n ≤ m := AA.inject ‹step n ≤ step m›
  exact le_split ‹n ≤ m›

theorem lt_trans {n m k : ℕ} : n < m → m < k → n < k := by
  intro (_ : n < m) (_ : m < k)
  show n < k
  apply lt_step_le.mpr
  show step n ≤ k
  calc
    _ ≤ step n := Eqv.refl
    _ ≤ m      := lt_step_le.mp ‹n < m›
    _ ≤ step m := le_from_lt lt_step
    _ ≤ k      := lt_step_le.mp ‹m < k›

instance : Relation.Trans (α := ℕ) (· < ·) where
  trans := lt_trans

theorem trichotomy {n m : ℕ}
    : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m) := by
  constructor
  case atLeastOne =>
    let motive := λ n => AA.OneOfThree (n < m) (n ≃ m) (n > m)
    apply Axioms.ind_on (motive := motive) n
    case zero =>
      show AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      let motive := λ m : ℕ => AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      apply Axioms.cases_on (motive := motive) m
      case zero =>
        apply AA.OneOfThree.second
        show 0 ≃ 0
        exact Eqv.refl
      case step =>
        intro m
        apply AA.OneOfThree.first
        show 0 < step m
        apply Order.Base.lt_defn.mpr
        apply And.intro
        · show 0 ≤ step m
          apply Order.Base.le_defn.mpr
          exists step m
          exact Addition.zero_add
        · show 0 ≄ step m
          exact Eqv.symm Axioms.step_neq_zero
    case step =>
      intro n (ih : AA.OneOfThree (n < m) (n ≃ m) (n > m))
      show AA.OneOfThree (step n < m) (step n ≃ m) (step n > m)
      match ih with
      | AA.OneOfThree.first (_ : n < m) =>
        have : step n ≤ m := lt_step_le.mp ‹n < m›
        have : step n < m ∨ step n ≃ m := le_split ‹step n ≤ m›
        match ‹step n < m ∨ step n ≃ m› with
        | Or.inl (_ : step n < m) => exact AA.OneOfThree.first ‹step n < m›
        | Or.inr (_ : step n ≃ m) => exact AA.OneOfThree.second ‹step n ≃ m›
      | AA.OneOfThree.second (_ : n ≃ m) =>
        have : m ≃ n := Eqv.symm ‹n ≃ m›
        have : m ≤ n := le_from_eqv ‹m ≃ n›
        have : step m ≤ step n := AA.subst ‹m ≤ n›
        have : m < step n := lt_step_le.mpr ‹step m ≤ step n›
        apply AA.OneOfThree.third
        exact ‹m < step n›
      | AA.OneOfThree.third (_ : n > m) =>
        apply AA.OneOfThree.third
        show m < step n
        exact Eqv.trans ‹m < n› lt_step
  case atMostOne =>
    show ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    intro
    | AA.TwoOfThree.oneAndTwo (_ : n < m) (_ : n ≃ m) =>
      show False
      have ⟨_, (_ : n ≄ m)⟩ := Order.Base.lt_defn.mp ‹n < m›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.oneAndThree (_ : n < m) (_ : n > m) =>
      show False
      have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := Order.Base.lt_defn.mp ‹n < m›
      have ⟨(_ : m ≤ n), _⟩ := Order.Base.lt_defn.mp ‹n > m›
      have : n ≃ m := le_antisymm ‹n ≤ m› ‹m ≤ n›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.twoAndThree (_ : n ≃ m) (_ : n > m) =>
      show False
      have ⟨_, (_ : m ≄ n)⟩ := Order.Base.lt_defn.mp ‹n > m›
      exact absurd ‹n ≃ m› (Eqv.symm ‹m ≄ n›)

instance order_derived : Order.Derived ℕ where
  le_subst_step := inferInstance
  le_inject_step := inferInstance
  le_subst_eqv := inferInstance
  le_refl := inferInstance
  le_trans := inferInstance
  le_subst_add := inferInstance
  le_cancel_add := inferInstance
  le_antisymm := le_antisymm
  le_from_eqv := le_from_eqv
  le_from_lt := le_from_lt
  le_split := le_split
  lt_subst_eqv := inferInstance
  lt_trans := inferInstance
  lt_zero := lt_zero
  lt_step := lt_step
  lt_step_le := lt_step_le
  lt_split := lt_split
  trichotomy := trichotomy

end Natural
end Lean4Axiomatic