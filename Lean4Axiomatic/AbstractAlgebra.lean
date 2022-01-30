import Lean4Axiomatic.Eqv

open Relation (EqvOp Refl Swap Symm Trans)

namespace AA

inductive Hand where
| L | R

def forHand {α : Sort u} {β : Sort v} : Hand → (α → α → β) → (α → α → β)
| Hand.L => id
| Hand.R => flip

class Commutative {α : Type u} [EqvOp α] (f : α → α → α) where
  comm {x y : α} : f x y ≃ f y x

export Commutative (comm)

instance
    {α : Type u} [EqvOp α] (f : α → α → α) [Commutative f]
    : Swap f (· ≃ ·) where
  swap := comm

class Substitutive
    {α : Sort u} {β : Sort v}
    (f : α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  subst {x₁ x₂ : α} : rα x₁ x₂ → rβ (f x₁) (f x₂)

export Substitutive (subst)

class SubstitutiveForHand
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  subst₂
    {x₁ x₂ y : α} : rα x₁ x₂ → rβ (forHand hand f x₁ y) (forHand hand f x₂ y)

export SubstitutiveForHand (subst₂)

def substL
    {α : Sort u} {β : Sort v} {f : α → α → β}
    {rα : α → α → Prop} {rβ : β → β → Prop}
    [inst : SubstitutiveForHand Hand.L f rα rβ]  {x₁ x₂ y : α}
    : rα x₁ x₂ → rβ (f x₁ y) (f x₂ y) := subst₂ (hand := Hand.L)

def substR
    {α : Sort u} {β : Sort v} {f : α → α → β}
    {rα : α → α → Prop} {rβ : β → β → Prop}
    [SubstitutiveForHand Hand.R f rα rβ]  {x₁ x₂ y : α}
    : rα x₁ x₂ → rβ (f y x₁) (f y x₂) := subst₂ (hand := Hand.R)

def substR_from_substL_swap
    {α : Sort u} {β : Sort v} {f : α → α → β}
    {rα : α → α → Prop} {rβ : β → β → Prop}
    [Refl rβ] [Trans rβ] [Swap f rβ] [SubstitutiveForHand Hand.L f rα rβ]
    : SubstitutiveForHand Hand.R f rα rβ := by
  constructor
  intro x₁ x₂ y (_ : rα x₁ x₂)
  show rβ (f y x₁) (f y x₂)
  calc
    rβ _ (f y x₁) := Refl.refl
    rβ _ (f x₁ y) := Swap.swap
    rβ _ (f x₂ y) := AA.substL ‹rα x₁ x₂›
    rβ _ (f y x₂) := Swap.swap

class Substitutive₂
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : α → α → Prop) (rβ : β → β → Prop)
    where
  substitutiveL : SubstitutiveForHand Hand.L f rα rβ
  substitutiveR : SubstitutiveForHand Hand.R f rα rβ

attribute [instance] Substitutive₂.substitutiveL
attribute [instance] Substitutive₂.substitutiveR

instance neq.substL
    {α : Sort u} [EqvOp α]
    : SubstitutiveForHand Hand.L (α := α) (· ≄ ·) (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y (_ : x₁ ≃ x₂) (_ : x₁ ≄ y) (_ : x₂ ≃ y)
  show False
  apply ‹x₁ ≄ y›
  show x₁ ≃ y
  exact Eqv.trans ‹x₁ ≃ x₂› ‹x₂ ≃ y›   

instance
    {α : Sort u} [EqvOp α] : Substitutive₂ (α := α) (· ≄ ·) (· ≃ ·) (· → ·)
    where
  substitutiveL := inferInstance
  substitutiveR := substR_from_substL_swap
  
end AA
