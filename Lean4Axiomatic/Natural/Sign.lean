import Lean4Axiomatic.Natural.Addition

namespace ℕ

class SignBase (ℕ : Type) [Constructors ℕ] [Equality ℕ] where
  Positive (n : ℕ) : Prop := n ≄ 0
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

export SignBase (Positive)

class SignProperties (ℕ : Type) [AdditionBase ℕ] extends SignBase ℕ where
  positive_subst : AA.Substitutive Positive (· ≃ ·) (· → ·)
  positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

namespace Derived

variable {ℕ : Type}

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
  exact AA.substL (self := AA.neq.substL) ‹n₁ ≃ n₂› ‹n₁ ≄ 0›

instance
    [Constructors ℕ] [Equality ℕ] [SignBase ℕ]
    : AA.Substitutive (α := ℕ) Positive (· ≃ ·) (· → ·) where
  subst := positive_subst

theorem positive_step
    [Axioms ℕ] [SignBase ℕ] {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n := by
  apply cases_on (motive := λ n => Positive n → ∃ m, step m ≃ n) n
  case zero =>
    intro (_ : Positive (0 : ℕ))
    apply False.elim
    show False
    have : 0 ≄ 0 := SignBase.positive_defn.mp ‹Positive (0 : ℕ)›
    apply this
    show 0 ≃ 0
    exact Eqv.refl
  case step =>
    intro n (_ : Positive (step n))
    exists n
    show step n ≃ step n
    exact Eqv.refl

theorem positive_add
    [AdditionBase ℕ] [SignBase ℕ] {n m : ℕ}
    : Positive n → Positive (n + m) := by
  intro (_ : Positive n)
  show Positive (n + m)
  apply cases_on (motive := λ m => Positive (n + m)) m
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
  positive_step := positive_step
  positive_add := positive_add

end Derived

end ℕ
