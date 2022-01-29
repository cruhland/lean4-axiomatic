import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv
import Lean4Axiomatic.Operators

open Operators (TildeDash)
open Relation (EqvOp?)

namespace Natural

class Constructors (ℕ : Type) where
  zero : ℕ
  step : ℕ → ℕ

export Constructors (zero step)

def ofNatImpl {ℕ : Type} [Constructors ℕ] : Nat → ℕ
| 0 => zero
| n+1 => step (ofNatImpl n)

instance instOfNat {ℕ : Type} [Constructors ℕ] {n : Nat} : OfNat ℕ n where
  ofNat := ofNatImpl n

class Equality (ℕ : Type) where
  eqvOp? : EqvOp? ℕ

attribute [instance] Equality.eqvOp?

class Axioms (ℕ : Type) extends Constructors ℕ, Equality ℕ where
  step_substitutive : AA.Substitutive step (· ≃ ·) (· ≃ ·)
  step_injective {n m : ℕ} : step n ≃ step m → n ≃ m
  step_neq_zero {n : ℕ} : step n ≄ 0

  ind {motive : ℕ → Prop}
    : motive 0 → (∀ n, motive n → motive (step n)) → ∀ n, motive n

attribute [instance] Axioms.step_substitutive

class AdditionBase (ℕ : Type) extends Axioms ℕ where
  addOp : Add ℕ

  zero_add {m : ℕ} : 0 + m ≃ m
  step_add {n m : ℕ} : step n + m ≃ step (n + m)

attribute [instance] AdditionBase.addOp

class AdditionProperties (ℕ : Type) extends AdditionBase ℕ where
  add_zero {n : ℕ} : n + 0 ≃ n
  add_step {n m : ℕ} : n + step m ≃ step (n + m)

  add_subst : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·)
  add_comm : AA.Commutative (α := ℕ) (· + ·)
  add_assoc {n m k : ℕ} : (n + m) + k ≃ n + (m + k)
  cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k
  zero_sum_split {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0

class Addition (ℕ : Type) extends AdditionProperties ℕ

class SignBase (ℕ : Type) [Constructors ℕ] [Equality ℕ] where
  Positive (n : ℕ) : Prop := n ≄ 0
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

export SignBase (Positive)

class SignProperties (ℕ : Type) [AdditionBase ℕ] extends SignBase ℕ where
  positive_subst : AA.Substitutive Positive (· ≃ ·) (· → ·)
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

class OrderBase (ℕ : Type) [AdditionBase ℕ] where
  leOp : LE ℕ := LE.mk λ n m => ∃ k : ℕ, n + k ≃ m
  le_defn {n m : ℕ} : n ≤ m ↔ ∃ k : ℕ, n + k ≃ m

  ltOp : LT ℕ := LT.mk λ n m => n ≤ m ∧ n ≄ m
  lt_defn {n m : ℕ} : n < m ↔ n ≤ m ∧ n ≄ m

-- Higher priority than the stdlib definitions
attribute [instance default+1] OrderBase.leOp
attribute [instance default+1] OrderBase.ltOp

class Decl (ℕ : Type) where
  [toAddition : Addition ℕ]
  [toSignProperties : SignProperties ℕ]
  [toOrderBase : OrderBase ℕ]

attribute [instance] Decl.toAddition
attribute [instance] Decl.toSignProperties
attribute [instance] Decl.toOrderBase

namespace Derived

variable {ℕ : Type}

def recOn
    [Axioms ℕ] {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n :=
  Axioms.ind zero step n

def casesOn
    [Axioms ℕ] {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n :=
  recOn n zero (λ n ih => step n)

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
      have : n₁ ≃ n₂ := Axioms.step_injective ‹step n₁ ≃ step n₂›
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
    [AdditionBase ℕ] : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·) where
  substitutiveL := inferInstance
  substitutiveR := inferInstance

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
    apply Axioms.step_injective
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
  add_comm := inferInstance
  add_assoc := add_assoc
  cancel_add := cancel_add
  zero_sum_split := zero_sum_split

instance [Constructors ℕ] [Equality ℕ] : SignBase ℕ where
  positive_defn := Iff.intro id id

theorem positive_subst
    [Constructors ℕ] [Equality ℕ] [SignBase ℕ] {n₁ n₂ : ℕ}
    : n₁ ≃ n₂ → Positive n₁ → Positive n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : Positive n₁)
  show Positive n₂
  have : n₁ ≄ 0 := SignBase.positive_defn.mp ‹Positive n₁›
  apply SignBase.positive_defn.mpr
  show n₂ ≄ 0
  exact AA.substL (inst := AA.neq.substL) ‹n₁ ≃ n₂› ‹n₁ ≄ 0›

instance
    [Constructors ℕ] [Equality ℕ] [SignBase ℕ]
    : AA.Substitutive (α := ℕ) Positive (· ≃ ·) (· → ·) where
  subst := positive_subst

theorem positive_add
    [AdditionBase ℕ] [SignBase ℕ] {n m : ℕ}
    : Positive n → Positive (n + m) := by
  intro (_ : Positive n)
  show Positive (n + m)
  apply casesOn (motive := λ m => Positive (n + m)) m
  case zero =>
    show Positive (n + 0)
    apply AA.subst (rβ := (· → ·)) (Eqv.symm AdditionProperties.add_zero)
    exact ‹Positive n›
  case step =>
    intro m
    show Positive (n + step m)
    apply AA.subst (rβ := (· → ·)) (Eqv.symm AdditionProperties.add_step)
    show Positive (step (n + m))
    apply SignBase.positive_defn.mpr
    show step (n + m) ≄ 0
    exact Axioms.step_neq_zero

instance signProperties [AdditionBase ℕ] [SignBase ℕ] : SignProperties ℕ where
  positive_subst := inferInstance
  positive_add := positive_add

instance [AdditionBase ℕ] : OrderBase ℕ where
  le_defn {n m : ℕ} := Iff.intro id id
  lt_defn {n m : ℕ} := Iff.intro id id

end Derived

namespace ImplNat

instance : Constructors Nat where
  zero := Nat.zero
  step := Nat.succ

instance : EqvOp? Nat where
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq

instance : Equality Nat where
  eqvOp? := inferInstance

instance : AA.Substitutive (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  subst := congrArg step

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

def indImpl
    {motive : Nat → Sort v}
    (mz : motive 0) (ms : {n : Nat} → motive n → motive (Nat.succ n)) (n : Nat)
    : motive n :=
  match n with
  | Nat.zero => mz
  | Nat.succ n => ms (indImpl mz ms n)

instance : Axioms Nat where
  step_substitutive := inferInstance
  step_injective := succ_injective
  step_neq_zero := Nat.noConfusion
  -- 2022-01-11: Using `Nat.rec` directly here, gives the following error:
  -- code generator does not support recursor 'Nat.rec' yet, consider using
  -- 'match ... with' and/or structural recursion
  ind := indImpl

instance : AdditionBase Nat where
  addOp := inferInstance
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add

instance : Addition Nat := Addition.mk
instance : Decl Nat := Decl.mk

end ImplNat

end Natural
