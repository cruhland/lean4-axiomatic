import Lean4Axiomatic.Rational.Metric

/-!
# Rational numbers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Rational

open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Metric (abs)
open Lean4Axiomatic.Signed (sgn)
open Natural (pow_step pow_zero step)

/-! ## Derived properties for exponentiation to a natural number -/

section pow_nat

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

/-- TODO -/
theorem pow_scompatL_recip
    {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : (p^n)⁻¹ ≃ (p⁻¹)^n
    := by
  apply Natural.ind_on n
  case zero =>
    show (p^0)⁻¹ ≃ (p⁻¹)^0
    calc
      _ ≃ (p^0)⁻¹ := eqv_refl
      _ ≃ 1⁻¹     := recip_subst pow_zero
      _ ≃ 1       := recip_sqrt1
      _ ≃ (p⁻¹)^0 := eqv_symm pow_zero
  case step =>
    intro (n' : ℕ) (ih : (p^n')⁻¹ ≃ (p⁻¹)^n')
    show (p^(step n'))⁻¹ ≃ (p⁻¹)^(step n')
    calc
      _ ≃ (p^(step n'))⁻¹ := eqv_refl
      _ ≃ (p^n' * p)⁻¹    := recip_subst pow_step
      _ ≃ (p^n')⁻¹ * p⁻¹  := recip_compat_mul
      _ ≃ (p⁻¹)^n' * p⁻¹  := mul_substL ih
      _ ≃ (p⁻¹)^(step n') := eqv_symm pow_step

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

end pow_nat

/-! ## Axioms for exponentiation to an integer -/

/-- Operations for raising rational numbers to integer powers. -/
class Exponentiation.Ops
    {ℕ : outParam Type} (ℚ ℤ : Type)
    [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Core (ℤ := ℤ) ℚ]
    :=
  /-- Exponentiation to an integer power. -/
  _pow (p : ℚ) (a : ℤ) [AP (p ≄ 0)] : ℚ

/-- Enables the use of the `· ^ ·` operator for exponentiation. -/
infixr:80 " ^ " => Exponentiation.Ops._pow

/-- Properties of exponentiation to an integer. -/
class Exponentiation.Props
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]
    [Negation ℚ] [Sign ℚ] [Ops ℚ ℤ]
    :=
  /-- TODO -/
  pow_diff {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - (m:ℤ)) ≃ p^n / p^m

export Exponentiation.Props (pow_diff)

/-- All integer exponentiation axioms. -/
class Exponentiation
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]
    [Negation ℚ] [Sign ℚ]
    :=
  toOps : Exponentiation.Ops ℚ ℤ
  toProps : Exponentiation.Props ℚ

attribute [instance] Exponentiation.toOps
attribute [instance] Exponentiation.toProps

/-! ## Derived properties for exponentiation to an integer -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Negation ℚ] [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (· * ·)] [Exponentiation ℚ]

/-- TODO -/
theorem pow_substL
    {p₁ p₂ : ℚ} {a : ℤ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁^a ≃ p₂^a
    := by
  intro (_ : p₁ ≃ p₂)
  show p₁^a ≃ p₂^a
  apply Integer.ind_diff_on a
  intro (n : ℕ) (m : ℕ)
  show p₁^((n:ℤ) - (m:ℤ)) ≃ p₂^((n:ℤ) - (m:ℤ))
  calc
    _ ≃ p₁^((n:ℤ) - (m:ℤ)) := eqv_refl
    _ ≃ p₁^n / p₁^m        := pow_diff
    _ ≃ p₂^n / p₁^m        := div_substL (Natural.pow_substL ‹p₁ ≃ p₂›)
    _ ≃ p₂^n / p₂^m        := div_substR (Natural.pow_substL ‹p₁ ≃ p₂›)
    _ ≃ p₂^((n:ℤ) - (m:ℤ)) := eqv_symm pow_diff

/-- TODO -/
theorem pow_preserves_nonzero {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : p^a ≄ 0 := by
  apply Integer.ind_diff_on a
  intro (n : ℕ) (m : ℕ) (_ : p^((n:ℤ) - (m:ℤ)) ≃ 0)
  show False
  have : p^n / p^m ≃ 0 := eqv_trans (eqv_symm pow_diff) ‹p^((n:ℤ) - (m:ℤ)) ≃ 0›
  have : p^n ≃ 0 := div_eqv_0.mp this
  have : p^n ≄ 0 := Natural.pow_preserves_nonzero_base ‹AP (p ≄ 0)›.ev
  exact absurd ‹p^n ≃ 0› ‹p^n ≄ 0›

/-- TODO -/
instance pow_preserves_nonzero_inst
    {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : AP (p^a ≄ 0)
    :=
  AP.mk pow_preserves_nonzero

/-- TODO -/
theorem pow_substR
    {p : ℚ} {a₁ a₂ : ℤ} [AP (p ≄ 0)] : a₁ ≃ a₂ → p^a₁ ≃ p^a₂
    := by
  apply Integer.ind_diff_on a₁
  intro (n₁ : ℕ) (m₁ : ℕ)
  apply Integer.ind_diff_on a₂
  intro (n₂ : ℕ) (m₂ : ℕ)
  let a₁ := (n₁:ℤ); let a₂ := (n₂:ℤ); let b₁ := (m₁:ℤ); let b₂ := (m₂:ℤ)
  intro (_ : a₁ - b₁ ≃ a₂ - b₂)
  show p^(a₁ - b₁) ≃ p^(a₂ - b₂)

  have : a₁ + b₂ ≃ a₂ + b₁ := Integer.sub_swap_add.mp ‹a₁ - b₁ ≃ a₂ - b₂›
  have : (((n₁ + m₂):ℕ):ℤ) ≃ (((m₁ + n₂):ℕ):ℤ) := calc
    _ ≃ (((n₁ + m₂):ℕ):ℤ) := Rel.refl
    _ ≃ (n₁:ℤ) + (m₂:ℤ)   := AA.compat₂
    _ ≃ a₁ + b₂           := Rel.refl
    _ ≃ a₂ + b₁           := ‹a₁ + b₂ ≃ a₂ + b₁›
    _ ≃ b₁ + a₂           := AA.comm
    _ ≃ (m₁:ℤ) + (n₂:ℤ)   := Rel.refl
    _ ≃ (((m₁ + n₂):ℕ):ℤ) := Rel.symm AA.compat₂
  have : n₁ + m₂ ≃ m₁ + n₂ := AA.inject this

  have : p^n₁ * p^m₂ ≃ p^(n₁ + m₂) := Rel.symm Natural.pow_compatL_add
  have : p^m₁ * p^n₂ ≃ p^(m₁ + n₂) := Rel.symm Natural.pow_compatL_add
  have : p^(n₁ + m₂) ≃ p^(m₁ + n₂) := Natural.pow_substR ‹n₁ + m₂ ≃ m₁ + n₂›
  have : p^(a₁ - b₁) / p^(a₂ - b₂) ≃ 1 := calc
    _ ≃ p^(a₁ - b₁) / p^(a₂ - b₂)     := eqv_refl
    _ ≃ (p^n₁ / p^m₁) / p^(a₂ - b₂)   := div_substL pow_diff
    _ ≃ (p^n₁ / p^m₁) / (p^n₂ / p^m₂) := div_substR pow_diff
    _ ≃ (p^n₁ * p^m₂) / (p^m₁ * p^n₂) := div_div_div
    _ ≃ p^(n₁ + m₂) / (p^m₁ * p^n₂)   := div_substL ‹p^n₁ * p^m₂ ≃ p^(n₁ + m₂)›
    _ ≃ p^(n₁ + m₂) / p^(m₁ + n₂)     := div_substR ‹p^m₁ * p^n₂ ≃ p^(m₁ + n₂)›
    _ ≃ p^(m₁ + n₂) / p^(m₁ + n₂)     := div_substL ‹p^(n₁ + m₂) ≃ p^(m₁ + n₂)›
    _ ≃ 1                             := div_same

  have : p^(a₁ - b₁) ≃ p^(a₂ - b₂) := div_eqv_1.mp this
  exact this

/-- TODO -/
theorem pow_nonneg {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : p^(n:ℤ) ≃ p^n := calc
  _ ≃ p^(n:ℤ)       := eqv_refl
  _ ≃ p^((n:ℤ) - 0) := pow_substR (Rel.symm Integer.sub_identR)
  _ ≃ p^n / p^(0:ℕ) := pow_diff
  _ ≃ p^n / 1       := div_substR Natural.pow_zero
  _ ≃ p^n           := div_identR

/-- TODO -/
theorem pow_neg {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : p^(-(n:ℤ)) ≃ (p⁻¹)^n := calc
  _ ≃ p^(-(n:ℤ))    := eqv_refl
  _ ≃ p^(0 - (n:ℤ)) := pow_substR (Rel.symm Integer.sub_identL)
  _ ≃ p^(0:ℕ) / p^n := pow_diff
  _ ≃ 1 / p^n       := div_substL Natural.pow_zero
  _ ≃ (p^n)⁻¹       := div_identL
  _ ≃ (p⁻¹)^n       := pow_scompatL_recip

end Lean4Axiomatic.Rational
