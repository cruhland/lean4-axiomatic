import Lean4Axiomatic.Integer.Order

/-!
# Integers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Integer

open Natural (step)
open Signed (Positive)

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

/-- TODO -/
theorem pow_preserves_pos {a : ℤ} {n : ℕ} : a > 0 → a^n > 0 := by
  intro (_ : a > 0)
  show a^n > 0
  have : sgn a ≃ 1 := gt_zero_sgn.mp ‹a > 0›
  have : sgn (a^n) ≃ 1 := calc
    _ = sgn (a^n) := rfl
    _ ≃ (sgn a)^n := sgn_pow
    _ ≃ 1^n       := Natural.pow_substL ‹sgn a ≃ 1›
    _ ≃ 1         := Natural.pow_absorbL
  have : a^n > 0 := gt_zero_sgn.mpr ‹sgn (a^n) ≃ 1›
  exact this

/-- TODO -/
theorem pow_preserves_nonneg {a : ℤ} {n : ℕ} : a ≥ 0 → a^n ≥ 0 := sorry

/-- TODO -/
theorem pow_pos_preserves_gt_pos
    {a b : ℤ} {n : ℕ} : n > 0 → b ≥ 0 → a > b → a^n > b^n
    := by
  intro (_ : n > 0) (_ : b ≥ 0) (_ : a > b)
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
        _ ≃ x^(step 0)  := Natural.pow_substR (AA.subst₁ ‹n' ≃ 0›)
        _ ≃ x^1         := Natural.pow_substR (Rel.symm Natural.literal_step)
        _ ≃ x           := Natural.pow_one
      calc
        _ = a^(step n') := rfl
        _ ≃ a           := pow_step_reduce
        _ > b           := ‹a > b›
        _ ≃ b^(step n') := Rel.symm pow_step_reduce
    | Or.inr (_ : n' > 0) =>
      have : a > 0 := trans ‹a > b› ‹b ≥ 0›
      have : b^n' ≥ 0 := pow_preserves_nonneg ‹b ≥ 0›
      have : sgn (a - b) ≃ 1 := gt_sgn.mp ‹a > b›
      have : a^n' > b^n' := ih ‹n' > 0›
      have : sgn (a^n' - b^n') ≃ 1 := gt_sgn.mp ‹a^n' > b^n'›
      have : sgn (a^n' * a - b^n' * a) ≃ 1 := calc
        _ = sgn (a^n' * a - b^n' * a) := rfl
        _ ≃ sgn ((a^n' - b^n') * a)   := sgn_subst (Rel.symm AA.distribR)
        _ ≃ sgn (a^n' - b^n') * sgn a := sgn_compat_mul
        _ ≃ 1 * sgn a                 := AA.substL ‹sgn (a^n' - b^n') ≃ 1›
        _ ≃ sgn a                     := AA.identL
        _ ≃ 1                         := gt_zero_sgn.mp ‹a > 0›
      have : sgn (b^n' * a - b^n' * b) ≥ 0 := calc
        _ = sgn (b^n' * a - b^n' * b) := rfl
        _ ≃ sgn (b^n' * (a - b))      := sgn_subst (Rel.symm AA.distribL)
        _ ≃ sgn (b^n') * sgn (a - b)  := sgn_compat_mul
        _ ≃ sgn (b^n') * 1            := AA.substR ‹sgn (a - b) ≃ 1›
        _ ≃ sgn (b^n')                := AA.identR
        _ ≥ 0                         := sgn_preserves_ge_zero.mp ‹b^n' ≥ 0›
      calc
        _ = a^(step n') := rfl
        _ ≃ a^n' * a    := Natural.pow_step
        _ > b^n' * a    := gt_sgn.mpr ‹sgn (a^n' * a - b^n' * a) ≃ 1›
        _ ≥ b^n' * b    := sgn_diff_ge_zero.mpr ‹sgn (b^n' * a - b^n' * b) ≥ 0›
        _ ≃ b^(step n') := Rel.symm Natural.pow_step

/-- TODO -/
theorem pow_preserves_ge_nonneg
    {a b : ℤ} {n : ℕ} : b ≥ 0 → a ≥ b → a^n ≥ b^n
    := by
  intro (_ : b ≥ 0) (_ : a ≥ b)
  show a^n ≥ b^n
  have : a > b ∨ b ≃ a := le_iff_lt_or_eqv.mp ‹a ≥ b›
  match this with
  | Or.inl (_ : a > b) =>
    have : n > 0 ∨ n ≃ 0 := Natural.ge_split Natural.ge_zero
    match this with
    | Or.inl (_ : n > 0) =>
      have : a^n > b^n := pow_pos_preserves_gt_pos ‹n > 0› ‹b ≥ 0› ‹a > b›
      have : a^n ≥ b^n := le_iff_lt_or_eqv.mpr (Or.inl ‹a^n > b^n›)
      exact this
    | Or.inr (_ : n ≃ 0) =>
      calc
        _ = a^n := rfl
        _ ≃ a^0 := Natural.pow_substR ‹n ≃ 0›
        _ ≥ 1   := le_iff_lt_or_eqv.mpr (Or.inr (Rel.symm Natural.pow_zero))
        _ ≃ b^0 := Rel.symm Natural.pow_zero
        _ ≃ b^n := Natural.pow_substR (Rel.symm ‹n ≃ 0›)
  | Or.inr (_ : b ≃ a) =>
    have : b^n ≃ a^n := Natural.pow_substL ‹b ≃ a›
    have : a^n ≥ b^n := le_iff_lt_or_eqv.mpr (Or.inr ‹b^n ≃ a^n›)
    exact this

theorem mul_identR_reasons {a b : ℤ} : a * b ≃ a ↔ a ≃ 0 ∨ b ≃ 1 := sorry

theorem sgn_step {n : ℕ} : sgn (step n : ℤ) ≃ 1 := sorry

theorem pow_sgn_even {a : ℤ} {n : ℕ} : (sgn a)^(2 * n) ≃ (sgn a)^2 := sorry

theorem pow_sgn_odd {a : ℤ} {n : ℕ} : (sgn a)^(2 * n + 1) ≃ sgn a := sorry

theorem sgn_absorb_pow
    {a : ℤ} {n : ℕ} : a ≥ 0 → n > 0 → (sgn a)^n ≃ sgn a
    := by
  admit

theorem sgn_squared_ge_zero {a : ℤ} : (sgn a)^2 ≥ 0 := sorry

/-- TODO -/
theorem sgn_sum_pos_prod
    {a b : ℤ} : a * b > 0 → sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
    := by
  intro (_ : a * b > 0)
  show sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
  let sum_formula (x y : ℤ) : ℤ := x + y - x * y^2
  have (And.intro (_ : sgn a ≃ sgn b) _) :=
    mul_gt_zero_iff_sgn_same.mp ‹a * b > 0›
  have sum_same {x y : ℤ} : x ≃ y → sum_formula x y ≃ y + y - y^(2*1+1) := by
    intro (_ : x ≃ y)
    show sum_formula x y ≃ y + y - y^(2*1+1)
    have : x * y^2 ≃ y^(2*1+1) := calc
      _ = x * y^2    := rfl
      _ ≃ y * y^2    := AA.substL ‹x ≃ y›
      _ ≃ y^2 * y    := AA.comm
      _ ≃ y^(step 2) := Rel.symm Natural.pow_step
      _ ≃ y^3        := Natural.pow_substR (Rel.symm Natural.literal_step)
      _ ≃ y^(2*1+1)  := Natural.pow_substR Natural.three_odd
    calc
      _ = sum_formula x y   := rfl
      _ = x + y - x * y^2   := rfl
      _ ≃ y + y - x * y^2   := sub_substL (AA.substL ‹x ≃ y›)
      _ ≃ y + y - y^(2*1+1) := sub_substR ‹x * y^2 ≃ y^(2*1+1)›
  let s := sum_formula (sgn a) (sgn b)
  have : s ≃ sgn b := calc
    _ = s                                   := rfl
    _ = sgn a + sgn b - (sgn a) * (sgn b)^2 := rfl
    _ ≃ sgn b + sgn b - (sgn b)^(2 * 1 + 1) := sum_same ‹sgn a ≃ sgn b›
    _ ≃ sgn b + sgn b - sgn b               := sub_substR pow_sgn_odd
    _ ≃ sgn b + (sgn b - sgn b)             := sub_assoc_addL
    _ ≃ sgn b + 0                           := AA.substR sub_same
    _ ≃ sgn b                               := AA.identR
  have : sgn b ≃ s := Rel.symm ‹s ≃ sgn b›
  have : sgn a ≃ s := Rel.trans ‹sgn a ≃ sgn b› ‹sgn b ≃ s›
  have : sgn (a + b) ≃ s := add_preserves_sign ‹sgn a ≃ s› ‹sgn b ≃ s›
  exact this

/-- TODO -/
theorem sgn_sum_zero_prod
    {a b : ℤ} : a * b ≃ 0 → sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
    := by
  intro (_ : a * b ≃ 0)
  show sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
  have sgn_sum_zeroL {x y : ℤ} : x ≃ 0 → sgn (x + y) ≃ sgn x + sgn y := by
    intro (_ : x ≃ 0)
    show sgn (x + y) ≃ sgn x + sgn y
    calc
      _ = sgn (x + y)   := rfl
      _ ≃ sgn (0 + y)   := sgn_subst (AA.substL ‹x ≃ 0›)
      _ ≃ sgn y         := sgn_subst AA.identL
      _ ≃ 0 + sgn y     := Rel.symm AA.identL
      _ ≃ sgn x + sgn y := AA.substL (Rel.symm (sgn_zero.mp ‹x ≃ 0›))
  have : a ≃ 0 ∨ b ≃ 0 := mul_split_zero.mp ‹a * b ≃ 0›
  have : sgn (a + b) ≃ sgn a + sgn b :=
    match ‹a ≃ 0 ∨ b ≃ 0› with
    | Or.inl (_ : a ≃ 0) =>
      sgn_sum_zeroL ‹a ≃ 0›
    | Or.inr (_ : b ≃ 0) =>
      calc
        _ = sgn (a + b)   := rfl
        _ ≃ sgn (b + a)   := sgn_subst AA.comm
        _ ≃ sgn b + sgn a := sgn_sum_zeroL ‹b ≃ 0›
        _ ≃ sgn a + sgn b := AA.comm
  have : a * b^2 ≃ 0 := calc
    _ = a * b^2        := rfl
    _ ≃ a * b^(step 1) := AA.substR (Natural.pow_substR Natural.literal_step)
    _ ≃ a * (b^1 * b)  := AA.substR Natural.pow_step
    _ ≃ a * (b * b^1)  := AA.substR AA.comm
    _ ≃ (a * b) * b^1  := Rel.symm AA.assoc
    _ ≃ 0 * b^1        := AA.substL ‹a * b ≃ 0›
    _ ≃ 0              := AA.absorbL
  have : (sgn a) * (sgn b)^2 ≃ 0 := calc
    _ = (sgn a) * (sgn b)^2   := rfl
    _ ≃ (sgn a) * (sgn (b^2)) := AA.substR (Rel.symm sgn_pow)
    _ ≃ sgn (a * b^2)         := Rel.symm sgn_compat_mul
    _ ≃ sgn (0:ℤ)             := sgn_subst ‹a * b^2 ≃ 0›
    _ ≃ 0                     := sgn_zero.mp Rel.refl
  have zero_eqv_sgn_prod := Rel.symm ‹(sgn a) * (sgn b)^2 ≃ 0›
  calc
    _ = sgn (a + b)                         := rfl
    _ ≃ sgn a + sgn b                       := ‹sgn (a + b) ≃ sgn a + sgn b›
    _ ≃ sgn a + sgn b - 0                   := Rel.symm sub_identR
    _ ≃ sgn a + sgn b - (sgn a) * (sgn b)^2 := sub_substR zero_eqv_sgn_prod

/-- TODO -/
theorem sgn_sum
    {a b : ℤ} : a * b ≥ 0 → sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
    := by
  intro (_ : a * b ≥ 0)
  show sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
  have : a * b > 0 ∨ a * b ≃ 0 := ge_split.mp ‹a * b ≥ 0›
  exact match this with
  | Or.inl (_ : a * b > 0) =>
    sgn_sum_pos_prod ‹a * b > 0›
  | Or.inr (_ : a * b ≃ 0) =>
    sgn_sum_zero_prod ‹a * b ≃ 0›

def sum_sub_err (a b : ℤ) : ℤ := a + b - a * b^2

theorem sse_substL
    {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → sum_sub_err a₁ b ≃ sum_sub_err a₂ b
    := by
  intro (_ : a₁ ≃ a₂)
  show sum_sub_err a₁ b ≃ sum_sub_err a₂ b
  calc
    _ = sum_sub_err a₁ b  := rfl
    _ = a₁ + b - a₁ * b^2 := rfl
    _ ≃ a₂ + b - a₁ * b^2 := sub_substL (AA.substL ‹a₁ ≃ a₂›)
    _ ≃ a₂ + b - a₂ * b^2 := sub_substR (AA.substL ‹a₁ ≃ a₂›)
    _ = sum_sub_err a₂ b  := rfl

theorem sse_substR
    {a b₁ b₂ : ℤ} : b₁ ≃ b₂ → sum_sub_err a b₁ ≃ sum_sub_err a b₂
    := by
  intro (_ : b₁ ≃ b₂)
  show sum_sub_err a b₁ ≃ sum_sub_err a b₂
  have : b₁^2 ≃ b₂^2 := Natural.pow_substL ‹b₁ ≃ b₂›
  calc
    _ = sum_sub_err a b₁  := rfl
    _ = a + b₁ - a * b₁^2 := rfl
    _ ≃ a + b₂ - a * b₁^2 := sub_substL (AA.substR ‹b₁ ≃ b₂›)
    _ ≃ a + b₂ - a * b₂^2 := sub_substR (AA.substR ‹b₁^2 ≃ b₂^2›)
    _ = sum_sub_err a b₂  := rfl

theorem sse_compat_mul
    {a b c : ℤ}
    : a^3 ≃ a → sum_sub_err (a * b) (a * c) ≃ a * sum_sub_err b c
    := by
  intro (_ : a^3 ≃ a)
  show sum_sub_err (a * b) (a * c) ≃ a * sum_sub_err b c
  have : a * a^2 ≃ a := calc
    _ = a * a^2    := rfl
    _ ≃ a^2 * a    := AA.comm
    _ ≃ a^(step 2) := Rel.symm Natural.pow_step
    _ ≃ a^3        := Natural.pow_substR (Rel.symm Natural.literal_step)
    _ ≃ a          := ‹a^3 ≃ a›
  have pull_out_a : (a * b) * (a * c)^2 ≃ a * (b * c^2) := calc
    _ = (a * b) * (a * c)^2   := rfl
    _ ≃ (a * b) * (a^2 * c^2) := AA.substR Natural.pow_distribR_mul
    _ ≃ (a * a^2) * (b * c^2) := AA.expr_xxfxxff_lr_swap_rl
    _ ≃ a * (b * c^2)         := AA.substL ‹a * a^2 ≃ a›
  calc
    _ = sum_sub_err (a * b) (a * c)         := rfl
    _ = a * b + a * c - (a * b) * (a * c)^2 := rfl
    _ ≃ a * (b + c) - (a * b) * (a * c)^2   := sub_substL (Rel.symm AA.distribL)
    _ ≃ a * (b + c) - a * (b * c^2)         := sub_substR pull_out_a
    _ ≃ a * (b + c - b * c^2)               := Rel.symm AA.distribL
    _ = a * sum_sub_err b c                 := rfl

theorem sgn_diff_pow_pos
    {a b : ℤ} {n : ℕ} : a ≥ 0 → b ≥ 0 → n > 0 → sgn (a^n - b^n) ≃ sgn (a - b)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  show n > 0 → sgn (a^n - b^n) ≃ sgn (a - b)
  apply Natural.ind_on n
  case zero =>
    intro (_ : (0:ℕ) > 0)
    show sgn (a^0 - b^0) ≃ sgn (a - b)
    have : (0:ℕ) ≯ 0 := Natural.lt_zero
    exact absurd ‹(0:ℕ) > 0› ‹(0:ℕ) ≯ 0›
  case step =>
    intro (m : ℕ) (ih : m > 0 → sgn (a^m - b^m) ≃ sgn (a - b)) (_ : step m > 0)
    show sgn (a^(step m) - b^(step m)) ≃ sgn (a - b)
    have : m ≥ 0 := Natural.ge_zero
    have : m > 0 ∨ m ≃ 0 := Natural.ge_split ‹m ≥ 0›
    match this.symm with
    | Or.inl (_ : m ≃ 0) =>
      have drop_pow {x : ℤ} : x^(step m) ≃ x := calc
        _ = x^(step m) := rfl
        _ ≃ x^(step 0) := Natural.pow_substR (AA.subst₁ ‹m ≃ 0›)
        _ ≃ x^1        := Natural.pow_substR (Rel.symm Natural.literal_step)
        _ ≃ x          := Natural.pow_one
      calc
        _ = sgn (a^(step m) - b^(step m)) := rfl
        _ ≃ sgn (a - b^(step m))          := sgn_subst (sub_substL drop_pow)
        _ ≃ sgn (a - b)                   := sgn_subst (sub_substR drop_pow)
    | Or.inr (_ : m > 0) =>
      have : a * b ≥ 0 := mul_preserves_ge_zero ‹a ≥ 0› ‹b ≥ 0›
      have : sgn (a * b) ≥ 0 := sgn_preserves_ge_zero.mp ‹a * b ≥ 0›
      have : a + b ≥ 0 := calc
        _ = a + b := rfl
        _ ≥ 0 + 0 := ge_add ‹a ≥ 0› ‹b ≥ 0›
        _ ≃ 0     := AA.identL
      have : a + b > 0 ∨ a + b ≃ 0 := ge_split.mp ‹a + b ≥ 0›
      have : sgn (a - b) ≃ 0 ∨ sgn (a + b) ≃ 1 := match this with
      | Or.inl (_ : a + b > 0) =>
        have : sgn (a + b) ≃ 1 := gt_zero_sgn.mp ‹a + b > 0›
        Or.inr ‹sgn (a + b) ≃ 1›
      | Or.inr (_ : a + b ≃ 0) =>
        have : a + b ≃ 0 ∧ a * b ≥ 0 := And.intro ‹a + b ≃ 0› ‹a * b ≥ 0›
        have (And.intro (_ : a ≃ 0) (_ : b ≃ 0)) :=
          sum_zero_prod_nonneg_iff_both_zero.mp ‹a + b ≃ 0 ∧ a * b ≥ 0›
        have : sgn (a - b) ≃ 0 := calc
          _ = sgn (a - b)     := rfl
          _ ≃ sgn (0 - b)     := sgn_subst (sub_substL ‹a ≃ 0›)
          _ ≃ sgn ((0:ℤ) - 0) := sgn_subst (sub_substR ‹b ≃ 0›)
          _ ≃ sgn (0:ℤ)       := sgn_subst sub_same
          _ ≃ 0               := sgn_zero.mp Rel.refl
        Or.inl ‹sgn (a - b) ≃ 0›
      let sab := sgn (a - b)
      let sam := sgn (a^m)
      let amab := a^m * (a - b)
      let abmb := (a^m - b^m) * b
      have sub_to_sum
          {w x y z : ℤ} : w*x - y*z ≃ w * (x - z) + (w - y) * z
          := calc
        _ = w*x - y*z                 := rfl
        _ ≃ (w*x - w*z) + (w*z - y*z) := Rel.symm add_sub_telescope
        _ ≃ w * (x - z) + (w*z - y*z) := AA.substL (Rel.symm AA.distribL)
        _ ≃ w * (x - z) + (w - y) * z := AA.substR (Rel.symm AA.distribR)
      have expand
          : a^(step m) - b^(step m) ≃ a^m * (a - b) + (a^m - b^m) * b
          := calc
        _ = a^(step m) - b^(step m)         := rfl
        _ ≃ a^m * a - b^(step m)            := sub_substL Natural.pow_step
        _ ≃ a^m * a - b^m * b               := sub_substR Natural.pow_step
        _ ≃ a^m * (a - b) + (a^m - b^m) * b := sub_to_sum
      have factor_sumL : sgn (a^m * (a - b)) ≃ sgn (a - b) * sgn (a^m) := calc
        _ = sgn (a^m * (a - b))     := rfl
        _ ≃ sgn (a^m) * sgn (a - b) := sgn_compat_mul
        _ ≃ sgn (a - b) * sgn (a^m) := AA.comm
      have factor_sumR : sgn ((a^m - b^m) * b) ≃ sgn (a - b) * sgn b := calc
        _ = sgn ((a^m - b^m) * b)   := rfl
        _ ≃ sgn (a^m - b^m) * sgn b := sgn_compat_mul
        _ ≃ sgn (a - b) * sgn b     := AA.substL (ih ‹m > 0›)
      have sgn_cubed {x : ℤ} : (sgn x)^3 ≃ sgn x := calc
        _ = (sgn x)^3           := rfl
        _ ≃ (sgn x)^(2 * 1 + 1) := Natural.pow_substR Natural.three_odd
        _ ≃ sgn x               := pow_sgn_odd
      have : sgn (a^m) ≃ sgn a := calc
        _ = sgn (a^m) := rfl
        _ ≃ (sgn a)^m := sgn_pow
        _ ≃ sgn a     := sgn_absorb_pow ‹a ≥ 0› ‹m > 0›
      -- TODO: fit within margin
      have : sgn ((a^m * (a - b)) * ((a^m - b^m) * b)) ≥ 0 := calc
        _ = sgn ((a^m * (a - b)) * ((a^m - b^m) * b))         := rfl
        _ ≃ sgn (a^m * (a - b)) * sgn ((a^m - b^m) * b)       := sgn_compat_mul
        _ ≃ (sgn (a - b) * sgn (a^m)) * sgn ((a^m - b^m) * b) := AA.substL factor_sumL
        _ ≃ (sgn (a - b) * sgn a) * sgn ((a^m - b^m) * b)     := AA.substL (AA.substR ‹sgn (a^m) ≃ sgn a›)
        _ ≃ (sgn (a - b) * sgn a) * (sgn (a - b) * sgn b)     := AA.substR factor_sumR
        _ ≃ (sgn (a - b) * sgn (a - b)) * (sgn a * sgn b)     := AA.expr_xxfxxff_lr_swap_rl
        _ ≃ (sgn (a - b))^2 * (sgn a * sgn b)                 := AA.substL (Rel.symm Natural.pow_two)
        _ ≃ (sgn (a - b))^2 * sgn (a * b)                     := AA.substR (Rel.symm sgn_compat_mul)
        _ ≥ 0                                                 := mul_preserves_ge_zero sgn_squared_ge_zero ‹sgn (a * b) ≥ 0›
      have terms_prod_nonneg : (a^m * (a - b)) * ((a^m - b^m) * b) ≥ 0 :=
        sgn_preserves_ge_zero.mpr this
      have reduce : sum_sub_err (sgn (a^m)) (sgn b) ≃ sgn (a + b) := calc
        _ = sum_sub_err (sgn (a^m)) (sgn b) := rfl
        _ ≃ sum_sub_err (sgn a) (sgn b)     := sse_substL ‹sgn (a^m) ≃ sgn a›
        _ ≃ sgn (a + b)                     := Rel.symm (sgn_sum ‹a * b ≥ 0›)
      have factor_sgn_sum : sgn (amab + abmb) ≃ sgn (a-b) * sgn (a+b) := calc
        _ = sgn (amab + abmb)                     := rfl
        _ ≃ sum_sub_err (sgn amab) (sgn abmb)     := sgn_sum terms_prod_nonneg
        _ ≃ sum_sub_err (sab * sam) (sgn abmb)    := sse_substL factor_sumL
        _ ≃ sum_sub_err (sab * sam) (sab * sgn b) := sse_substR factor_sumR
        _ ≃ sab * sum_sub_err sam (sgn b)         := sse_compat_mul sgn_cubed
        _ = sgn (a-b) * sum_sub_err sam (sgn b)   := rfl
        _ ≃ sgn (a-b) * sgn (a+b)                 := AA.substR reduce
      have drop_sgn_sum : sgn (a - b) * sgn (a + b) ≃ sgn (a - b) :=
        mul_identR_reasons.mpr ‹sgn (a - b) ≃ 0 ∨ sgn (a + b) ≃ 1›
      calc
        _ = sgn (a^(step m) - b^(step m))         := rfl
        _ ≃ sgn (a^m * (a - b) + (a^m - b^m) * b) := sgn_subst expand
        _ ≃ sgn (a - b) * sgn (a + b)             := factor_sgn_sum
        _ ≃ sgn (a - b)                           := drop_sgn_sum

/-- TODO -/
theorem sgn_diff_pow
    {a b : ℤ} {n : ℕ}
    : a ≥ 0 → b ≥ 0 → sgn (a^n - b^n) ≃ sgn (a - b) * sgn (n:ℤ)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  show sgn (a^n - b^n) ≃ sgn (a - b) * sgn (n:ℤ)
  have : n ≥ 0 := Natural.ge_zero
  have : n > 0 ∨ n ≃ 0 := Natural.ge_split ‹n ≥ 0›
  match this.symm with
  | Or.inl (_ : n ≃ 0) =>
    have : a^n - b^n ≃ (n:ℤ) := calc
      _ = a^n - b^n := rfl
      _ ≃ a^0 - b^n := sub_substL (Natural.pow_substR ‹n ≃ 0›)
      _ ≃ a^0 - b^0 := sub_substR (Natural.pow_substR ‹n ≃ 0›)
      _ ≃ 1 - b^0   := sub_substL Natural.pow_zero
      _ ≃ (1:ℤ) - 1 := sub_substR Natural.pow_zero
      _ ≃ 0         := zero_diff_iff_eqv.mpr Rel.refl
      _ ≃ (n:ℤ)     := AA.subst₁ (Rel.symm ‹n ≃ 0›)
    have : sgn (n:ℤ) ≃ 0 := calc
      _ = sgn (n:ℤ)     := rfl
      _ ≃ sgn ((0:ℕ):ℤ) := sgn_subst (AA.subst₁ ‹n ≃ 0›)
      _ ≃ 0             := sgn_zero.mp Rel.refl
    calc
      _ = sgn (a^n - b^n)         := rfl
      _ ≃ sgn (n:ℤ)               := sgn_subst ‹a^n - b^n ≃ (n:ℤ)›
      _ ≃ 0                       := ‹sgn (n:ℤ) ≃ 0›
      _ ≃ sgn (a - b) * 0         := Rel.symm AA.absorbR
      _ ≃ sgn (a - b) * sgn (n:ℤ) := AA.substR (Rel.symm ‹sgn (n:ℤ) ≃ 0›)
  | Or.inr (_ : n > 0) =>
    have : Positive n := Natural.lt_zero_pos.mpr ‹n > 0›
    have : Positive (n:ℤ) := positive_intro_nat ‹Positive n› Rel.refl
    have : sgn (n:ℤ) ≃ 1 := sgn_positive.mp ‹Positive (n:ℤ)›
    calc
      _ = sgn (a^n - b^n)         := rfl
      _ ≃ sgn (a - b)             := sgn_diff_pow_pos ‹a ≥ 0› ‹b ≥ 0› ‹n > 0›
      _ ≃ sgn (a - b) * 1         := Rel.symm AA.identR
      _ ≃ sgn (a - b) * sgn (n:ℤ) := AA.substR (Rel.symm ‹sgn (n:ℤ) ≃ 1›)

end Lean4Axiomatic.Integer
