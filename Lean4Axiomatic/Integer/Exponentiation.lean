import Lean4Axiomatic.Integer.Order

/-!
# Integers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Integer

open Natural (step)

/-! ## Derived properties for exponentiation to a natural number -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]
  [Negation ℤ] [Subtraction ℤ] [Sign ℤ] [Order ℤ]
  [Natural.Exponentiation ℕ ℤ (· * ·)]

/-- TODO -/
theorem sgn_pow {a : ℤ} {n : ℕ} : sgn (a^n) ≃ (sgn a)^n := by
  apply Natural.ind_on n
  case zero =>
    show sgn (a^0) ≃ (sgn a)^0
    calc
      _ = sgn (a^0) := rfl
      _ ≃ sgn (1:ℤ) := sgn_subst Natural.pow_zero
      _ ≃ 1         := sgn_positive.mp one_positive
      _ ≃ (sgn a)^0 := Rel.symm Natural.pow_zero
  case step =>
    intro (n' : ℕ) (ih : sgn (a^n') ≃ (sgn a)^n')
    show sgn (a^(step n')) ≃ (sgn a)^(step n')
    calc
      _ = sgn (a^(step n'))  := rfl
      _ ≃ sgn (a^n' * a)     := sgn_subst Natural.pow_step
      _ ≃ sgn (a^n') * sgn a := sgn_compat_mul
      _ ≃ (sgn a)^n' * sgn a := AA.substL ih
      _ ≃ (sgn a)^(step n')  := Rel.symm Natural.pow_step

theorem pow_preserves_pos {a : ℤ} {n : ℕ} : a > 0 → a^n > 0 := sorry

theorem pow_pos_preserves_gt_pos
    {a b : ℤ} {n : ℕ} : b > 0 → n > 0 → a > b → a^n > b^n
    := by
  intro (_ : b > 0) (_ : n > 0) (_ : a > b)
  revert ‹n > 0›
  show n > 0 → a^n > b^n

  apply Natural.ind_on n
  case zero =>
    intro (_ : (0:ℕ) > 0)
    show a^0 > b^0
    have : (0:ℕ) ≯ 0 := Natural.lt_zero
    exact absurd ‹(0:ℕ) > 0› ‹(0:ℕ) ≯ 0›
  case step =>
    intro (n' : ℕ) (ih : n' > 0 → a^n' > b^n') (_ : step n' > 0)
    show a^(step n') > b^(step n')
    have : n' ≃ 0 ∨ n' > 0 := Natural.gt_split ‹step n' > 0›
    match this with
    | Or.inl (_ : n' ≃ 0) =>
      have pow_step_reduce {x : ℤ} : x^(step n') ≃ x := calc
        _ = x^(step n') := rfl
        _ ≃ x^n' * x    := Natural.pow_step
        _ ≃ x^0 * x     := AA.substL (Natural.pow_substR ‹n' ≃ 0›)
        _ ≃ 1 * x       := AA.substL Natural.pow_zero
        _ ≃ x           := AA.identL
      calc
        _ = a^(step n') := rfl
        _ ≃ a           := pow_step_reduce
        _ > b           := ‹a > b›
        _ ≃ b^(step n') := Rel.symm pow_step_reduce
    | Or.inr (_ : n' > 0) =>
      have : a > 0 := trans ‹a > b› ‹b > 0›
      have : b^n' > 0 := pow_preserves_pos ‹b > 0›
      have : sgn (a - b) ≃ 1 := gt_sgn.mp ‹a > b›
      have : a^n' > b^n' := ih ‹n' > 0›
      have : sgn (a^n' - b^n') ≃ 1 := gt_sgn.mp ‹a^n' > b^n'›
      -- TODO: these next two items could be generalized
      have : sgn (a^n' * a - b^n' * a) ≃ 1 := calc
        _ = sgn (a^n' * a - b^n' * a) := rfl
        _ ≃ sgn ((a^n' - b^n') * a)   := sgn_subst (Rel.symm AA.distribR)
        _ ≃ sgn (a^n' - b^n') * sgn a := sgn_compat_mul
        _ ≃ 1 * sgn a                 := AA.substL ‹sgn (a^n' - b^n') ≃ 1›
        _ ≃ sgn a                     := AA.identL
        _ ≃ 1                         := gt_zero_sgn.mp ‹a > 0›
      have : sgn (b^n' * a - b^n' * b) ≃ 1 := calc
        _ = sgn (b^n' * a - b^n' * b) := rfl
        _ ≃ sgn (b^n' * (a - b))      := sgn_subst (Rel.symm AA.distribL)
        _ ≃ sgn (b^n') * sgn (a - b)  := sgn_compat_mul
        _ ≃ sgn (b^n') * 1            := AA.substR ‹sgn (a - b) ≃ 1›
        _ ≃ sgn (b^n')                := AA.identR
        _ ≃ 1                         := gt_zero_sgn.mp ‹b^n' > 0›
      have : sgn (a^(step n') - b^(step n')) ≃ 1 := calc
        _ = sgn (a^(step n') - b^(step n'))                     := rfl
        _ ≃ sgn (a^n' * a - b^(step n'))                        := sgn_subst (sub_substL Natural.pow_step)
        _ ≃ sgn (a^n' * a - b^n' * b)                           := sgn_subst (sub_substR Natural.pow_step)
        _ ≃ sgn ((a^n' * a - b^n' * a) + (b^n' * a - b^n' * b)) := sgn_subst (Rel.symm add_sub_telescope)
        _ ≃ 1                                                   := add_preserves_sign ‹sgn (a^n' * a - b^n' * a) ≃ 1› ‹sgn (b^n' * a - b^n' * b) ≃ 1›
      have : a^(step n') > b^(step n') := gt_sgn.mpr this
      exact this

end Lean4Axiomatic.Integer
