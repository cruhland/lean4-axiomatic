import Lean4Axiomatic.Rational.Metric

/-!
# Rational numbers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Rational

open Lean4Axiomatic.Metric (abs)
open Lean4Axiomatic.Signed (sgn)
open Natural (pow_step pow_zero step)

/-! ## Derived properties -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Negation ℚ] [Subtraction ℚ] [Reciprocation ℚ] [Division ℚ]
    [Sign ℚ] [Order ℚ] [Metric ℚ] [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]

/--
Raising two ordered, nonnegative values to the same natural number power
preserves their ordering and nonnegativity.

**Property intuition**: We already know that products of any nonnegative values
remain nonnegative, and that the greater the inputs, the greater the result. So
it's not surprising that this also holds for powers of nonnegative values.

**Proof intuition**: Induction and algebra. Substitutions on ordering relations
are the key steps.
-/
theorem pow_substL_ge_nonneg
    {p q : ℚ} {n : ℕ} : p ≥ q ∧ q ≥ 0 → p^n ≥ q^n ∧ q^n ≥ 0
    := by
  intro (And.intro (_ : p ≥ q) (_ : q ≥ 0))
  show p^n ≥ q^n ∧ q^n ≥ 0
  apply Natural.ind_on n
  case zero =>
    show p^0 ≥ q^0 ∧ q^0 ≥ 0
    have : p^(0:ℕ) ≥ q^(0:ℕ) := calc
      _ ≃ p^0 := eqv_refl
      _ ≃ 1   := pow_zero
      _ ≃ q^0 := eqv_symm pow_zero
      _ ≥ q^0 := le_refl
    have : q^(0:ℕ) ≥ 0 := calc
      _ ≃ q^0 := eqv_refl
      _ ≃ 1   := pow_zero
      _ ≥ 0   := one_ge_zero
    exact And.intro ‹p^(0:ℕ) ≥ q^(0:ℕ)› ‹q^(0:ℕ) ≥ 0›
  case step =>
    intro (n' : ℕ) (And.intro (_ : p^n' ≥ q^n') (_ : q^n' ≥ 0))
    show p^(step n') ≥ q^(step n') ∧ q^(step n') ≥ 0
    have : p ≥ 0 := ge_trans ‹p ≥ q› ‹q ≥ 0›
    have : p^(step n') ≥ q^(step n') := calc
      _ ≃ p^(step n') := eqv_refl
      _ ≃ p^n' * p    := pow_step
      _ ≥ q^n' * p    := le_substL_mul_nonneg ‹p ≥ 0› ‹p^n' ≥ q^n'›
      _ ≥ q^n' * q    := le_substR_mul_nonneg ‹q^n' ≥ 0› ‹p ≥ q›
      _ ≃ q^(step n') := eqv_symm pow_step
    have : q^(step n') ≥ 0 := calc
      _ ≃ q^(step n') := eqv_refl
      _ ≃ q^n' * q    := pow_step
      _ ≥ 0 * q       := le_substL_mul_nonneg ‹q ≥ 0› ‹q^n' ≥ 0›
      _ ≃ 0           := mul_absorbL
    exact And.intro ‹p^(step n') ≥ q^(step n')› ‹q^(step n') ≥ 0›

/--
Raising two strictly ordered, nonnegative values to the same positive natural
number power preserves their strict ordering and nonnegativity.

**Property intuition**: We already know that products of any nonnegative values
remain nonnegative, and that the greater the inputs, the greater the result. So
it's not surprising that this also holds for powers of nonnegative values.

**Proof intuition**: Induction and algebra. Substitutions on ordering relations
are the key steps. The base case is a contradiction because `n > 0` is an
assumption, so there's a case split inside the inductive step to handle the
"real" base case of `n ≃ 1`.
-/
theorem pow_pos_substL_gt_nonneg
    {p q : ℚ} {n : ℕ} : n > 0 → p > q ∧ q ≥ 0 → p^n > q^n ∧ q^n ≥ 0
    := by
  intro (_ : n > 0) (And.intro (_ : p > q) (_ : q ≥ 0))
  revert ‹n > 0›
  show n > 0 → p^n > q^n ∧ q^n ≥ 0
  apply Natural.ind_on n
  case zero =>
    intro (_ : (0:ℕ) > 0)
    show p^0 > q^0 ∧ q^0 ≥ 0
    have : (0:ℕ) ≯ 0 := Natural.lt_zero
    exact absurd ‹(0:ℕ) > 0› ‹(0:ℕ) ≯ 0›
  case step =>
    intro (n' : ℕ) (ih : n' > 0 → p^n' > q^n' ∧ q^n' ≥ 0) (_ : step n' > 0)
    show p^(step n') > q^(step n') ∧ q^(step n') ≥ 0
    have : n' ≃ 0 ∨ n' > 0 := Natural.gt_split ‹step n' > 0›
    match this with
    | Or.inl (_ : n' ≃ 0) =>
      have pow_step_zero {x : ℚ} : x^(step n') ≃ x := calc
        _ ≃ x^(step n') := eqv_refl
        _ ≃ x^n' * x    := pow_step
        _ ≃ x^0 * x     := mul_substL (Natural.pow_substR ‹n' ≃ 0›)
        _ ≃ 1 * x       := mul_substL pow_zero
        _ ≃ x           := mul_identL
      have : p^(step n') > q^(step n') := calc
        _ ≃ p^(step n') := eqv_refl
        _ ≃ p           := pow_step_zero
        _ > q           := ‹p > q›
        _ ≃ q^(step n') := eqv_symm pow_step_zero
      have : q^(step n') ≥ 0 := calc
        _ ≃ q^(step n') := eqv_refl
        _ ≃ q           := pow_step_zero
        _ ≥ 0           := ‹q ≥ 0›
      exact And.intro ‹p^(step n') > q^(step n')› ‹q^(step n') ≥ 0›
    | Or.inr (_ : n' > 0) =>
      have (And.intro (_ : p^n' > q^n') (_ : q^n' ≥ 0)) := ih ‹n' > 0›
      have : p ≥ q := ge_cases.mpr (Or.inl ‹p > q›)
      have : p > 0 := trans_gt_ge_gt ‹p > q› ‹q ≥ 0›
      have : p^(step n') > q^(step n') := calc
        _ ≃ p^(step n') := eqv_refl
        _ ≃ p^n' * p    := pow_step
        _ > q^n' * p    := lt_substL_mul_pos ‹p > 0› ‹p^n' > q^n'›
        _ ≥ q^n' * q    := le_substR_mul_nonneg ‹q^n' ≥ 0› ‹p ≥ q›
        _ ≃ q^(step n') := eqv_symm pow_step
      have : q^(step n') ≥ 0 := calc
        _ ≃ q^(step n') := eqv_refl
        _ ≃ q^n' * q    := pow_step
        _ ≥ 0 * q       := le_substL_mul_nonneg ‹q ≥ 0› ‹q^n' ≥ 0›
        _ ≃ 0           := mul_absorbL
      exact And.intro ‹p^(step n') > q^(step n')› ‹q^(step n') ≥ 0›

/--
Absolute value is semicompatible with the base argument of exponentiation.

**Property intuition**: Absolute value is compatible with multiplication, so
applying it to repeated multiplication means that it gets applied to every
factor in the expression.

**Proof intuition**: Induction and algebra.
-/
theorem pow_scompatL_abs {p : ℚ} {n : ℕ} : abs (p^n) ≃ (abs p)^n := by
  apply Natural.ind_on n
  case zero =>
    show abs (p^0) ≃ (abs p)^0
    have : sgn (1:ℚ) ≃ 1 := sgn_one
    have : abs (1:ℚ) ≃ 1 := abs_positive this
    calc
      _ ≃ abs (p^0) := eqv_refl
      _ ≃ abs 1     := abs_subst pow_zero
      _ ≃ 1         := ‹abs (1:ℚ) ≃ 1›
      _ ≃ (abs p)^0 := eqv_symm pow_zero
  case step =>
    intro (n' : ℕ) (ih : abs (p^n') ≃ (abs p)^n')
    show abs (p^(step n')) ≃ (abs p)^(step n')
    calc
      _ ≃ abs (p^(step n'))  := eqv_refl
      _ ≃ abs (p^n' * p)     := abs_subst pow_step
      _ ≃ abs (p^n') * abs p := abs_compat_mul
      _ ≃ (abs p)^n' * abs p := mul_substL ih
      _ ≃ (abs p)^(step n')  := eqv_symm pow_step

end Lean4Axiomatic.Rational
