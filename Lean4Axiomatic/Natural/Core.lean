import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv

namespace ℕ

open Relation (EqvOp?)

variable {ℕ : Type}

class Constructors (ℕ : Type) where
  zero : ℕ
  step : ℕ → ℕ

export Constructors (zero step)

def ofNat {ℕ : Type} [Constructors ℕ] : Nat → ℕ
| 0 => zero
| n+1 => step (ofNat n)

instance instOfNat {ℕ : Type} [Constructors ℕ] {n : Nat} : OfNat ℕ n where
  ofNat := ofNat n

class Equality (ℕ : Type) where
  eqvOp? : EqvOp? ℕ

attribute [instance] Equality.eqvOp?

class Axioms (ℕ : Type) extends Constructors ℕ, Equality ℕ where
  step_substitutive : AA.Substitutive step (· ≃ ·) (· ≃ ·)
  step_injective : AA.Injective step (· ≃ ·) (· ≃ ·)
  step_neq_zero {n : ℕ} : step n ≄ 0

  ind {motive : ℕ → Prop}
    : motive 0 → (∀ n, motive n → motive (step n)) → ∀ n, motive n

attribute [instance] Axioms.step_substitutive
attribute [instance] Axioms.step_injective

class Axioms.Derived (ℕ : Type) [Axioms ℕ] where
  ind_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n

  cases_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n

  step_neq {n : ℕ} : step n ≄ n

def ind_on
    [Axioms ℕ] {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n :=
  Axioms.ind zero step n

def cases_on
    [Axioms ℕ] {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n :=
  ind_on n zero (λ n ih => step n)

instance [Axioms ℕ] : Axioms.Derived ℕ where
  ind_on := ind_on
  cases_on := cases_on

  step_neq {n : ℕ} : step n ≄ n := by
    apply ind_on (motive := λ n => step n ≄ n) n
    case zero =>
      show step 0 ≄ 0
      exact Axioms.step_neq_zero
    case step =>
      intro n (ih : step n ≄ n)
      show step (step n) ≄ step n
      intro (_ : step (step n) ≃ step n)
      show False
      apply ih
      show step n ≃ n
      exact AA.inject ‹step (step n) ≃ step n›

end ℕ
