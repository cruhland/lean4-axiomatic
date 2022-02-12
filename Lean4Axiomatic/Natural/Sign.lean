import Lean4Axiomatic.Natural.Addition

namespace ℕ

class Sign.Base (ℕ : Type) [Core ℕ] where
  Positive (n : ℕ) : Prop := n ≄ 0
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

class Sign.Derived (ℕ : Type) [Core ℕ] [Addition.Base ℕ]
    extends Sign.Base ℕ where
  positive_subst : AA.Substitutive Positive (· ≃ ·) (· → ·)
  positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

export Sign.Base (Positive)

namespace Derived

variable {ℕ : Type}
variable [Core ℕ]

instance : Sign.Base ℕ where
  positive_defn := Iff.intro id id

theorem positive_subst
    [Sign.Base ℕ] {n₁ n₂ : ℕ} : n₁ ≃ n₂ → Positive n₁ → Positive n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : Positive n₁)
  show Positive n₂
  have : n₁ ≄ 0 := Sign.Base.positive_defn.mp ‹Positive n₁›
  apply Sign.Base.positive_defn.mpr
  show n₂ ≄ 0
  exact AA.substL (self := AA.neq.substL) ‹n₁ ≃ n₂› ‹n₁ ≄ 0›

instance
    [Core ℕ] [Sign.Base ℕ]
    : AA.Substitutive (α := ℕ) Positive (· ≃ ·) (· → ·) where
  subst := positive_subst

theorem positive_step
    [Axioms.Derived ℕ] [Sign.Base ℕ] {n : ℕ}
    : Positive n → ∃ m : ℕ, step m ≃ n := by
  apply Axioms.cases_on (motive := λ n => Positive n → ∃ m, step m ≃ n) n
  case zero =>
    intro (_ : Positive (0 : ℕ))
    apply False.elim
    show False
    have : 0 ≄ 0 := Sign.Base.positive_defn.mp ‹Positive (0 : ℕ)›
    apply this
    show 0 ≃ 0
    exact Eqv.refl
  case step =>
    intro n (_ : Positive (step n))
    exists n
    show step n ≃ step n
    exact Eqv.refl

theorem positive_add
    [Axioms.Derived ℕ] [Addition.Derived ℕ] [Sign.Base ℕ] {n m : ℕ}
    : Positive n → Positive (n + m) := by
  intro (_ : Positive n)
  show Positive (n + m)
  apply Axioms.cases_on (motive := λ m => Positive (n + m)) m
  case zero =>
    show Positive (n + 0)
    apply AA.subst (rβ := (· → ·)) (Eqv.symm Addition.add_zero)
    exact ‹Positive n›
  case step =>
    intro m
    show Positive (n + step m)
    apply AA.subst (rβ := (· → ·)) (Eqv.symm Addition.add_step)
    show Positive (step (n + m))
    apply Sign.Base.positive_defn.mpr
    show step (n + m) ≄ 0
    exact Axioms.step_neq_zero

instance signProperties
    [Axioms.Derived ℕ] [Addition.Derived ℕ] [Sign.Base ℕ]
    : Sign.Derived ℕ where
  positive_subst := inferInstance
  positive_step := positive_step
  positive_add := positive_add

end Derived

end ℕ
