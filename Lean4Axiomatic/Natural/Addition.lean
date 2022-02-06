import Lean4Axiomatic.Natural.Core

namespace ℕ

class AdditionBase (ℕ : Type) extends Axioms ℕ where
  addOp : Add ℕ

  zero_add {m : ℕ} : 0 + m ≃ m
  step_add {n m : ℕ} : step n + m ≃ step (n + m)

attribute [instance] AdditionBase.addOp

class AdditionProperties (ℕ : Type) extends AdditionBase ℕ where
  add_zero {n : ℕ} : n + 0 ≃ n
  add_step {n m : ℕ} : n + step m ≃ step (n + m)
  add_subst : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·)
  add_one_step {n : ℕ} : n + 1 ≃ step n
  add_comm : AA.Commutative (α := ℕ) (· + ·)
  add_assoc {n m k : ℕ} : (n + m) + k ≃ n + (m + k)
  cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k
  zero_sum_split {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0

class Addition (ℕ : Type) extends AdditionProperties ℕ

namespace Derived

variable {ℕ : Type}

theorem add_zero [AdditionBase ℕ] {n : ℕ} : n + 0 ≃ n := by
  apply recOn (motive := λ n => n + 0 ≃ n) n
  case zero =>
    show 0 + 0 ≃ 0
    calc
      _ ≃ 0 + (0 : ℕ) := Eqv.refl
      _ ≃ 0           := AdditionBase.zero_add
  case step =>
    intro n (ih : n + 0 ≃ n)
    show step n + 0 ≃ step n
    calc
      _ ≃ step n + 0   := Eqv.refl
      _ ≃ step (n + 0) := AdditionBase.step_add
      _ ≃ step n       := AA.subst ih

theorem add_step [AdditionBase ℕ] {n m : ℕ} : n + step m ≃ step (n + m) := by
  apply recOn (motive := λ n => n + step m ≃ step (n + m)) n
  case zero =>
    show 0 + step m ≃ step (0 + m)
    calc
      _ ≃ 0 + step m   := Eqv.refl
      _ ≃ step m       := AdditionBase.zero_add
      _ ≃ step (0 + m) := AA.subst (Eqv.symm AdditionBase.zero_add)
  case step =>
    intro n (ih : n + step m ≃ step (n + m))
    show step n + step m ≃ step (step n + m)
    calc
      _ ≃ step n + step m     := Eqv.refl
      _ ≃ step (n + step m)   := AdditionBase.step_add
      _ ≃ step (step (n + m)) := AA.subst ih
      _ ≃ step (step n + m)   := AA.subst (Eqv.symm AdditionBase.step_add)

theorem add_comm [AdditionBase ℕ] {n m : ℕ} : n + m ≃ m + n := by
  apply recOn (motive := λ n => n + m ≃ m + n) n
  case zero =>
    show 0 + m ≃ m + 0
    calc
      _ ≃ 0 + m := Eqv.refl
      _ ≃ m     := AdditionBase.zero_add
      _ ≃ m + 0 := Eqv.symm add_zero
  case step =>
    intro n (ih : n + m ≃ m + n)
    show step n + m ≃ m + step n
    calc
      _ ≃ step n + m   := Eqv.refl
      _ ≃ step (n + m) := AdditionBase.step_add
      _ ≃ step (m + n) := AA.subst ih
      _ ≃ m + step n   := Eqv.symm add_step

instance [AdditionBase ℕ] : AA.Commutative (α := ℕ) (· + ·) where
  comm := add_comm

theorem subst_add
    [AdditionBase ℕ] {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ + m ≃ n₂ + m := by
  apply recOn (motive := λ x => ∀ y, x ≃ y → x + m ≃ y + m) n₁
  case zero =>
    intro n₂
    show 0 ≃ n₂ → 0 + m ≃ n₂ + m
    apply casesOn (motive := λ y => 0 ≃ y → 0 + m ≃ y + m)
    case zero =>
      intro (_ : 0 ≃ (0 : ℕ))
      show 0 + m ≃ 0 + m
      exact Eqv.refl
    case step =>
      intro n₂ (_ : 0 ≃ step n₂)
      show 0 + m ≃ step n₂ + m
      apply False.elim
      show False
      exact Axioms.step_neq_zero (Eqv.symm ‹0 ≃ step n₂›)
  case step =>
    intro n₁ (ih : ∀ y, n₁ ≃ y → n₁ + m ≃ y + m) n₂
    show step n₁ ≃ n₂ → step n₁ + m ≃ n₂ + m
    apply casesOn (motive := λ y => step n₁ ≃ y → step n₁ + m ≃ y + m)
    case zero =>
      intro (_ : step n₁ ≃ 0)
      show step n₁ + m ≃ 0 + m
      apply False.elim
      show False
      exact Axioms.step_neq_zero ‹step n₁ ≃ 0›
    case step =>
      intro n₂ (_ : step n₁ ≃ step n₂)
      show step n₁ + m ≃ step n₂ + m
      have : n₁ ≃ n₂ := AA.inject ‹step n₁ ≃ step n₂›
      calc
        _ ≃ step n₁ + m   := Eqv.refl
        _ ≃ step (n₁ + m) := AdditionBase.step_add
        _ ≃ step (n₂ + m) := AA.subst (ih _ ‹n₁ ≃ n₂›)
        _ ≃ step n₂ + m   := Eqv.symm AdditionBase.step_add

instance [AdditionBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) where
  subst₂ := subst_add

instance [AdditionBase ℕ]
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) :=
  AA.substR_from_substL_swap

instance
    [AdditionBase ℕ] : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) :=
  AA.Substitutive₂.mk

theorem add_one_step [AdditionBase ℕ] {n : ℕ} : n + 1 ≃ step n := by
  calc
    _ ≃ n + 1        := Eqv.refl
    _ ≃ n + step 0   := AA.substR Eqv.refl
    _ ≃ step (n + 0) := add_step
    _ ≃ step n       := AA.subst add_zero

theorem add_assoc
    [AdditionBase ℕ] {n m k : ℕ} : (n + m) + k ≃ n + (m + k) := by
  apply recOn (motive := λ n => (n + m) + k ≃ n + (m + k)) n
  case zero =>
    show (0 + m) + k ≃ 0 + (m + k)
    calc
      _ ≃ (0 + m) + k := Eqv.refl
      _ ≃ m + k       := AA.substL AdditionBase.zero_add
      _ ≃ 0 + (m + k) := Eqv.symm (AdditionBase.zero_add)
  case step =>
    intro n (ih : (n + m) + k ≃ n + (m + k))
    show (step n + m) + k ≃ step n + (m + k)
    calc
      _ ≃ (step n + m) + k   := Eqv.refl
      _ ≃ step (n + m) + k   := AA.substL AdditionBase.step_add
      _ ≃ step ((n + m) + k) := AdditionBase.step_add
      _ ≃ step (n + (m + k)) := AA.subst ih
      _ ≃ step n + (m + k)   := Eqv.symm AdditionBase.step_add

theorem cancel_add [AdditionBase ℕ] {n m k : ℕ} : n + m ≃ n + k → m ≃ k := by
  apply recOn (motive := λ n => n + m ≃ n + k → m ≃ k) n
  case zero =>
    intro (_ : 0 + m ≃ 0 + k)
    show m ≃ k
    calc
      _ ≃ m     := Eqv.refl
      _ ≃ 0 + m := Eqv.symm AdditionBase.zero_add
      _ ≃ 0 + k := ‹0 + m ≃ 0 + k›
      _ ≃ k     := AdditionBase.zero_add
  case step =>
    intro n (ih : n + m ≃ n + k → m ≃ k) (_ : step n + m ≃ step n + k)
    show m ≃ k
    apply ih
    show n + m ≃ n + k
    apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
    show step (n + m) ≃ step (n + k)
    calc
      _ ≃ step (n + m) := Eqv.refl
      _ ≃ step n + m   := Eqv.symm AdditionBase.step_add
      _ ≃ step n + k   := ‹step n + m ≃ step n + k›
      _ ≃ step (n + k) := AdditionBase.step_add

theorem zero_sum_split
    [AdditionBase ℕ] {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0 := by
  apply casesOn (motive := λ n => n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0) n
  case zero =>
    intro (_ : 0 + m ≃ 0)
    show 0 ≃ 0 ∧ m ≃ 0
    have : m ≃ 0 := Eqv.trans (Eqv.symm AdditionBase.zero_add) ‹0 + m ≃ 0›
    exact ⟨Eqv.refl, ‹m ≃ 0›⟩
  case step =>
    intro n (_ : step n + m ≃ 0)
    show step n ≃ 0 ∧ m ≃ 0
    apply False.elim
    show False
    have : step (n + m) ≃ 0 :=
      Eqv.trans (Eqv.symm AdditionBase.step_add) ‹step n + m ≃ 0›
    exact Axioms.step_neq_zero ‹step (n + m) ≃ 0›

instance additionProperties [AdditionBase ℕ] : AdditionProperties ℕ where
  add_zero := add_zero
  add_step := add_step
  add_subst := inferInstance
  add_one_step := add_one_step
  add_comm := inferInstance
  add_assoc := add_assoc
  cancel_add := cancel_add
  zero_sum_split := zero_sum_split

end Derived

end ℕ
