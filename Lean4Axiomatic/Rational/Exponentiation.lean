import Lean4Axiomatic.Rational.Metric

/-!
# Rational numbers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Rational

open Lean4Axiomatic.Function (idx_fam_prop)
open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Metric (abs)
open Lean4Axiomatic.Natural (pow_step pow_zero step)
open Lean4Axiomatic.Signed (sgn)

/-! ## Derived properties for exponentiation to a natural number -/

section pow_nat

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Negation ℚ] [Subtraction ℚ] [Reciprocation ℚ] [Division ℚ]
    [Sign ℚ] [Order ℚ] [Metric ℚ] [Natural.Exponentiation ℕ ℚ (· * ·)]

/-- TODO -/
theorem pow_scompatL_from_integer {a : ℤ} {n : ℕ} : ((a^n:ℤ):ℚ) ≃ (a:ℚ)^n := by
  apply Natural.ind_on n
  case zero =>
    show ((a^0:ℤ):ℚ) ≃ (a:ℚ)^0
    calc
      _ = ((a^0:ℤ):ℚ) := rfl
      _ ≃ 1           := from_integer_subst Natural.pow_zero
      _ ≃ (a:ℚ)^0     := eqv_symm Natural.pow_zero
  case step =>
    intro (n' : ℕ) (ih : ((a^n':ℤ):ℚ) ≃ (a:ℚ)^n')
    show ((a^(step n'):ℤ):ℚ) ≃ (a:ℚ)^(step n')
    calc
      _ = ((a^(step n'):ℤ):ℚ)  := rfl
      _ ≃ ((a^n' * a : ℤ):ℚ)   := from_integer_subst Natural.pow_step
      _ ≃ ((a^n':ℤ):ℚ) * (a:ℚ) := mul_compat_from_integer
      _ ≃ (a:ℚ)^n' * (a:ℚ)     := mul_substL ih
      _ ≃ (a:ℚ)^(step n')      := eqv_symm Natural.pow_step

/--
Raising rationals to natural number powers is semicompatible with reciprocation
on the left operand.

**Property intuition**: Reciprocation and multiplication are compatible, so it
shouldn't matter if the multiplications for exponentiation happen first, or the
reciprocation.

**Proof intuition**: Use induction and the compatibility of multiplication and
reciprocation.
-/
theorem pow_scompatL_recip
    {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : (p^n)⁻¹ ≃ (p⁻¹)^n
    := by
  apply Natural.ind_on n
  case zero =>
    show (p^(0:ℕ))⁻¹ ≃ (p⁻¹)^(0:ℕ)
    calc
      _ = (p^(0:ℕ))⁻¹ := rfl
      _ ≃ 1⁻¹         := recip_subst pow_zero
      _ ≃ 1           := recip_sqrt1
      _ ≃ (p⁻¹)^(0:ℕ) := eqv_symm pow_zero
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
A natural number exponent distributes over division.

**Property intuition**: The product of two fractions is the product of their
numerators over the product of their denominators. Exponentiation is repeated
multiplication, so we'd expect the same pattern to hold.

**Proof intuition**: Convert division to multiplication by the reciprocal. Then
distribute the exponent over multiplication, and commute it with reciprocation.
-/
theorem pow_distribR_div
    {p q : ℚ} [AP (q ≄ 0)] {n : ℕ} : (p / q)^n ≃ p^n / q^n
    := calc
  _ = (p / q)^n     := rfl
  _ ≃ (p * q⁻¹)^n   := Natural.pow_substL div_mul_recip
  _ ≃ p^n * (q⁻¹)^n := Natural.pow_distribR_mul
  _ ≃ p^n * (q^n)⁻¹ := mul_substR (eqv_symm pow_scompatL_recip)
  _ ≃ p^n / q^n     := eqv_symm div_mul_recip

/-- TODO -/
theorem sgn_pow {p : ℚ} {n : ℕ} : sgn (p^n) ≃ (sgn p)^n := by
  have (AsRatio.intro (a : ℤ) (b : ℤ) (_ : Integer.Nonzero b) p_eqv) :=
    as_ratio p
  have : p ≃ a/b := p_eqv
  have int_sgn_pow {x : ℤ} : sgn ((x:ℚ)^n) ≃ (sgn x)^n := calc
    _ = sgn ((x:ℚ)^n)   := rfl
    _ ≃ sgn ((x^n:ℤ):ℚ) := sgn_subst (eqv_symm pow_scompatL_from_integer)
    _ ≃ sgn (x^n)       := sgn_from_integer
    _ ≃ (sgn x)^n       := Integer.sgn_pow
  have sgn_merge : sgn a * sgn b ≃ sgn p := calc
    _ = sgn a * sgn b         := rfl
    _ ≃ sgn (a:ℚ) * sgn b     := AA.substL (Rel.symm sgn_from_integer)
    _ ≃ sgn (a:ℚ) * sgn (b:ℚ) := AA.substR (Rel.symm sgn_from_integer)
    _ ≃ sgn ((a:ℚ)/b)         := Rel.symm sgn_div
    _ ≃ sgn p                 := sgn_subst (eqv_symm ‹p ≃ a/b›)
  calc
    _ = sgn (p^n)                     := rfl
    _ ≃ sgn (((a:ℚ)/b)^n)             := sgn_subst (Natural.pow_substL p_eqv)
    _ ≃ sgn ((a:ℚ)^n/b^n)             := sgn_subst pow_distribR_div
    _ ≃ sgn ((a:ℚ)^n) * sgn ((b:ℚ)^n) := sgn_div
    _ ≃ (sgn a)^n * sgn ((b:ℚ)^n)     := AA.substL int_sgn_pow
    _ ≃ (sgn a)^n * (sgn b)^n         := AA.substR int_sgn_pow
    _ ≃ (sgn a * sgn b)^n             := Rel.symm Natural.pow_distribR_mul
    _ ≃ (sgn p)^n                     := Natural.pow_substL sgn_merge

/-- TODO -/
theorem pow_preserves_pos {p : ℚ} {n : ℕ} : p > 0 → p^n > 0 := by
  intro (_ : p > 0)
  show p^n > 0
  have : sgn p ≃ 1 := gt_zero_sgn.mp ‹p > 0›
  have : sgn (p^n) ≃ 1 := calc
    _ = sgn (p^n) := rfl
    _ ≃ (sgn p)^n := sgn_pow
    _ ≃ 1^n       := Natural.pow_substL ‹sgn p ≃ 1›
    _ ≃ 1         := Natural.pow_absorbL
  have : p^n > 0 := gt_zero_sgn.mpr ‹sgn (p^n) ≃ 1›
  exact this

/-- TODO -/
theorem pow_preserves_nonneg {p : ℚ} {n : ℕ} : p ≥ 0 → p^n ≥ 0 := by
  intro (_ : p ≥ 0)
  show p^n ≥ 0

  have : p > 0 ∨ p ≃ 0 := ge_cases.mp ‹p ≥ 0›
  match this with
  | Or.inl (_ : p > 0) =>
    have : p^n > 0 := pow_preserves_pos ‹p > 0›
    have : p^n ≥ 0 := ge_cases.mpr (Or.inl ‹p^n > 0›)
    exact this
  | Or.inr (_ : p ≃ 0) =>
    have : (0:ℚ)^n ≃ 0 ∨ (0:ℚ)^n ≃ 1 := Natural.pow_of_zero
    match this with
    | Or.inl (_ : (0:ℚ)^n ≃ 0) =>
      calc
        _ = p^n := rfl
        _ ≃ 0^n := Natural.pow_substL ‹p ≃ 0›
        _ ≃ 0   := ‹(0:ℚ)^n ≃ 0›
        _ ≥ 0   := le_refl
    | Or.inr (_ : (0:ℚ)^n ≃ 1) =>
      calc
        _ = p^n := rfl
        _ ≃ 0^n := Natural.pow_substL ‹p ≃ 0›
        _ ≃ 1   := ‹(0:ℚ)^n ≃ 1›
        _ ≥ 0   := one_ge_zero

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

inductive NonnegRatio (p : ℚ) : Prop :=
| intro (a b : ℤ) (b_pos : AP ((b:ℚ) > 0)) (a_nneg : a ≥ 0) (p_eqv : p ≃ a / b) : NonnegRatio p

theorem as_nonneg_ratio {p : ℚ} : p ≥ 0 → NonnegRatio p := by
  admit

theorem pow_pos_preserves_gt_nonneg
    {p q : ℚ} {n : ℕ} : n > 0 → q ≥ 0 → p > q → p^n > q^n
    := by
  intro (_ : n > 0) (_ : q ≥ 0) (_ : p > q)
  show p^n > q^n
  have : p > 0 := trans ‹p > q› ‹q ≥ 0›
  have : p ≥ 0 := ge_cases.mpr (Or.inl ‹p > 0›)
  have (NonnegRatio.intro
      (a : ℤ) (b : ℤ) (_ : AP ((b:ℚ) > 0)) (_ : a ≥ 0) p_eqv)
      := as_nonneg_ratio ‹p ≥ 0›
  have : p ≃ a/b := p_eqv
  have (NonnegRatio.intro
      (c : ℤ) (d : ℤ) (_ : AP ((d:ℚ) > 0)) (_ : c ≥ 0) q_eqv)
      := as_nonneg_ratio ‹q ≥ 0›
  have : q ≃ c/d := q_eqv

  let aQn := (a:ℚ)^n; let bQn := (b:ℚ)^n
  let cQn := (c:ℚ)^n; let dQn := (d:ℚ)^n

  -- we need to prove that if p > q, then ad > bc!
  -- sgn (p - q) ≃ 1
  -- sgn ((a/b) - (c/d))
  -- sgn ((ad - bc)/(bd))
  -- sgn (ad - bc) ≃ 1 (QED)

  have sub_liftQ {x y : ℤ} : (x:ℚ) - y ≃ ((x - y : ℤ):ℚ) :=
    eqv_symm sub_compat_from_integer
  have mul_liftQ {x y : ℤ} : (x:ℚ) * y ≃ ((x * y : ℤ):ℚ) :=
    eqv_symm mul_compat_from_integer
  have mul_pow_liftQ
      {x y : ℤ} {k : ℕ} : (x:ℚ)^k * (y:ℚ)^k ≃ (((x * y)^k : ℤ):ℚ)
      := calc
    _ = (x:ℚ)^k * (y:ℚ)^k   := rfl
    _ ≃ ((x:ℚ) * y)^k       := eqv_symm Natural.pow_distribR_mul
    _ ≃ ((x * y : ℤ):ℚ)^k   := Natural.pow_substL mul_liftQ
    _ ≃ (((x * y)^k : ℤ):ℚ) := eqv_symm pow_scompatL_from_integer
  have sub_mul_liftQ
      : aQn * dQn - bQn * cQn ≃ (((a * d)^n - (b * c)^n : ℤ):ℚ)
      := calc
    _ = aQn * dQn - bQn * cQn                     := rfl
    _ ≃ (((a * d)^n : ℤ):ℚ) - bQn * cQn           := sub_substL mul_pow_liftQ
    _ ≃ (((a * d)^n : ℤ):ℚ) - (((b * c)^n : ℤ):ℚ) := sub_substR mul_pow_liftQ
    _ ≃ (((a * d)^n - (b * c)^n : ℤ):ℚ)           := sub_liftQ
  have sub_pow_expand : p^n - q^n ≃ (a:ℚ)^n/b^n - (c:ℚ)^n/d^n := calc
    _ = p^n - q^n                 := rfl
    _ ≃ ((a:ℚ)/b)^n - q^n         := sub_substL (Natural.pow_substL ‹p ≃ a/b›)
    _ ≃ ((a:ℚ)/b)^n - ((c:ℚ)/d)^n := sub_substR (Natural.pow_substL ‹q ≃ c/d›)
    _ ≃ (a:ℚ)^n/b^n - ((c:ℚ)/d)^n := sub_substL pow_distribR_div
    _ ≃ (a:ℚ)^n/b^n - (c:ℚ)^n/d^n := sub_substR pow_distribR_div
  have : AP (((b^n * d^n : ℤ):ℚ) ≄ 0) := sorry
  have : AP ((((b * d)^n : ℤ):ℚ) ≄ 0) := sorry
  have sub_pow_frac
      : p^n - q^n ≃ (((a * d)^n - (b * c)^n : ℤ):ℚ)/(((b * d)^n : ℤ):ℚ)
      := calc
    _ = p^n - q^n                               := rfl
    _ ≃ aQn/bQn - cQn/dQn                       := sub_pow_expand
    _ ≃ (aQn * dQn - bQn * cQn)/(bQn * dQn)     := sub_fractions
    _ ≃ (((a*d)^n-(b*c)^n:ℤ):ℚ)/(bQn * dQn)     := div_substL sub_mul_liftQ
    _ ≃ (((a*d)^n-(b*c)^n:ℤ):ℚ)/(((b*d)^n:ℤ):ℚ) := div_substR mul_pow_liftQ
  have : sgn (b * d) ≃ 1 := sorry
  have : Integer.Nonzero (b * d) := sorry
  have : (b * d)^n > 0 := sorry
  have : Integer.Nonzero ((b * d)^n) := sorry
  have : AP (((b * d : ℤ):ℚ) ≄ 0) := sorry
  have : sgn ((b * d)^n) ≃ 1 := Integer.gt_zero_sgn.mp ‹(b * d)^n > 0›
  have : b * c ≥ 0 := sorry
  have : sgn (a * d - b * c) ≃ 1 := calc
    _ = sgn (a * d - b * c) := rfl
    _ ≃ sgn (a * d - b * c) * 1 := Rel.symm AA.identR
    _ ≃ sgn (a * d - b * c) * sgn (b * d) := AA.substR (Rel.symm ‹sgn (b * d) ≃ 1›)
    _ ≃ sgn (((a * d - b * c : ℤ):ℚ)/(b * d : ℤ):ℚ) := Rel.symm sgn_div_integers
    _ ≃ 1 := sorry
  have : a * d > b * c := Integer.gt_sgn.mpr ‹sgn (a * d - b * c) ≃ 1›
  have : (a * d)^n > (b * c)^n :=
    Integer.pow_pos_preserves_gt_pos ‹n > 0› ‹b * c ≥ 0› ‹a * d > b * c›
  have sub_pow_pos : sgn ((a * d)^n - (b * c)^n) ≃ 1 := Integer.gt_sgn.mp this
  have : sgn (p^n - q^n) ≃ 1 := calc
    _ = sgn (p^n - q^n)                               := rfl
    _ ≃ sgn ((((a*d)^n-(b*c)^n:ℤ):ℚ)/(((b*d)^n:ℤ):ℚ)) := sgn_subst sub_pow_frac
    _ ≃ sgn ((a*d)^n-(b*c)^n) * sgn ((b*d)^n)         := sgn_div_integers
    _ ≃ 1 * sgn ((b*d)^n)                             := AA.substL sub_pow_pos
    _ ≃ sgn ((b*d)^n)                                 := AA.identL
    _ ≃ 1                                             := ‹sgn ((b * d)^n) ≃ 1›
  have : p^n > q^n := gt_sgn.mpr ‹sgn (p^n - q^n) ≃ 1›
  exact this

end pow_nat

/-
/-! ## Axioms for exponentiation to an integer -/

/-- Operations for raising rational numbers to integer powers. -/
class Exponentiation.Ops
    {ℕ : outParam Type} (ℚ ℤ : Type)
    [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Core (ℤ := ℤ) ℚ]
    :=
  /-- Exponentiation to an integer power. -/
  _pow (p : ℚ) [AP (p ≄ 0)] (a : ℤ) : ℚ

/-- Enables the use of the `· ^ ·` operator for exponentiation. -/
infixr:80 " ^ " => Exponentiation.Ops._pow

/-- Properties of exponentiation to an integer. -/
class Exponentiation.Props
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Natural.Exponentiation ℕ ℚ (· * ·)]
    [Negation ℚ] [Sign ℚ] [Ops ℚ ℤ]
    :=
  /--
  An equivalence between raising a rational number to the power of a
  difference, and the quotient of that rational number raised individually to
  each of the difference's components.

  **Intuition**: If `n` counts multiples of `p` to include in the final result,
  and `m` counts multiples of `p` to take away, then `p^n / p^m` denotes how to
  calculate it; the multiples on top and bottom cancel out. If we tried to
  represent this result using a single exponent, then `(n:ℤ) - (m:ℤ)` would be
  how to do it, as it captures the behavior of the cancellation.
  -/
  pow_diff {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - (m:ℤ)) ≃ p^n / p^m

  /--
  Rational number exponentiation to an integer respects equivalence of the
  exponents.

  **Intuition**: For exponentiation to make sense as a function on integers,
  this needs to be true.
  -/
  pow_substR {p : ℚ} [AP (p ≄ 0)] {a₁ a₂ : ℤ} : a₁ ≃ a₂ → p^a₁ ≃ p^a₂

export Exponentiation.Props (pow_diff pow_substR)

/-- All integer exponentiation axioms. -/
class Exponentiation
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Natural.Exponentiation ℕ ℚ (· * ·)]
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
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Subtraction ℚ] [Reciprocation ℚ] [Division ℚ] [Sign ℚ] [Order ℚ]
    [Natural.Exponentiation ℕ ℚ (· * ·)] [Exponentiation ℚ]

/--
Rational number exponentiation to an integer respects equivalence of the base
values.

**Property intuition**: For integer exponentiation to make sense as a function
on rationals, this needs to be true.

**Proof intuition**: Write the integer exponent as a difference of natural
numbers, and use `pow_diff` to convert the integer power into a ratio of
natural number powers. Then delegate to `Natural.pow_substL`.
-/
theorem pow_substL
    {p₁ p₂ : ℚ} {a : ℤ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁^a ≃ p₂^a
    := by
  intro (_ : p₁ ≃ p₂)
  show p₁^a ≃ p₂^a

  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  calc
    _ = p₁^a           := rfl
    _ ≃ p₁^((n:ℤ) - m) := pow_substR ‹a ≃ n - m›
    _ ≃ p₁^n / p₁^m    := pow_diff
    _ ≃ p₂^n / p₁^m    := div_substL (Natural.pow_substL ‹p₁ ≃ p₂›)
    _ ≃ p₂^n / p₂^m    := div_substR (Natural.pow_substL ‹p₁ ≃ p₂›)
    _ ≃ p₂^((n:ℤ) - m) := eqv_symm pow_diff
    _ ≃ p₂^a           := pow_substR (Rel.symm ‹a ≃ n - m›)

/--
Raising a nonzero rational number to any integer power gives a nonzero result.

**Property intuition**: As the product of two nonzero rational numbers is
nonzero, this is simply an extension of that fact to any number of
multiplications. "Negative" multiplications are accounted for because
reciprocals are always nonzero.

**Proof intuition**: Assume the contrary, and reach a contradiction. Write the
integer exponent as a difference of natural numbers, and use `pow_diff` to
convert the this into a quotient of natural number powers. Show that the
numerator must be zero (from the assumption) and nonzero (from the analogous
theorem for natural number powers), giving us the desired contradiction.
-/
theorem pow_preserves_nonzero {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : p^a ≄ 0 := by
  intro (_ : p^a ≃ 0)
  show False

  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  have : p^n / p^m ≃ 0 := calc
    _ = p^n / p^m     := rfl
    _ ≃ p^((n:ℤ) - m) := eqv_symm pow_diff
    _ ≃ p^a           := pow_substR (Rel.symm ‹a ≃ n - m›)
    _ ≃ 0             := ‹p^a ≃ 0›
  have : p^n ≃ 0 := div_eqv_0.mp this
  have : p^n ≄ 0 := Natural.pow_preserves_nonzero_base ‹AP (p ≄ 0)›.ev
  exact absurd ‹p^n ≃ 0› ‹p^n ≄ 0›

/-- Instance version of `pow_preserves_nonzero`. -/
instance pow_preserves_nonzero_inst
    {p : ℚ} {a : ℤ} [AP (p ≄ 0)] : AP (p^a ≄ 0)
    :=
  AP.mk pow_preserves_nonzero

/--
Raising a nonzero rational number to a nonnegative integer power is equivalent
to raising it to the corresponding natural number.

**Property intuition**: Natural numbers and nonnegative integers are
equivalent, and exponentiation respects equivalence.

**Proof intuition**: Convert the integer power into a difference of natural
numbers and simplify.
-/
theorem pow_nonneg {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : p^(n:ℤ) ≃ p^n := calc
  _ ≃ p^(n:ℤ)       := eqv_refl
  _ ≃ p^((n:ℤ) - 0) := pow_substR (Rel.symm Integer.sub_identR)
  _ ≃ p^n / p^(0:ℕ) := pow_diff
  _ ≃ p^n / 1       := div_substR Natural.pow_zero
  _ ≃ p^n           := div_identR

/--
Raising a nonzero rational number to a non-positive integer power is equivalent
to raising it to the natural number with the same absolute value, then taking
the reciprocal.

**Property intuition**: For addition of exponents to make sense, we need
negative values to "cancel out" the corresponding positive values. This can be
done if the negative values are reciprocals of the positives.

**Proof intuition**: Convert the integer power into a difference of natural
numbers and simplify.
-/
theorem pow_neg {p : ℚ} {n : ℕ} [AP (p ≄ 0)] : p^(-(n:ℤ)) ≃ 1 / p^n := calc
  _ = p^(-(n:ℤ))    := rfl
  _ ≃ p^(0 - (n:ℤ)) := pow_substR (Rel.symm Integer.sub_identL)
  _ ≃ p^(0:ℕ) / p^n := pow_diff
  _ ≃ 1 / p^n       := div_substL Natural.pow_zero

/--
Integer exponents add when powers of the same rational number are multiplied.

**Property intuition**: Exponentiation to integers is repeated multiplication,
either by the base (for positive exponents) or by the base's reciprocal (for
negative exponents). The exponent gives the number of repetitions. Thus if two
powers of the same base are multiplied, that's equivalent to the second power's
multiplication count being combined with the first power's count.

**Proof intuition**: Write both integer exponents as differences of natural
numbers. Invoke `pow_diff` to convert powers of differences to ratios of
natural number powers. Rearrange using algebra and the natural number version
of this property.
-/
theorem pow_compatL_add
    {p : ℚ} [AP (p ≄ 0)] {a b : ℤ} : p^(a + b) ≃ p^a * p^b
    := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a
  have Exists.intro (k : ℕ) (Exists.intro (j : ℕ) (_ : b ≃ k - j)) :=
    Integer.as_diff b
  have : a + b ≃ (n + k : ℕ) - (m + j : ℕ) := calc
    _ = a + b                     := rfl
    _ ≃ (n - m) + b               := AA.substL ‹a ≃ n - m›
    _ ≃ (n - m) + (k - j)         := AA.substR ‹b ≃ k - j›
    _ ≃ (n + k) - (m + j)         := Integer.sub_xchg_add
    _ ≃ (n + k : ℕ) - (m + j)     := AA.substL (Rel.symm AA.compat₂)
    _ ≃ (n + k : ℕ) - (m + j : ℕ) := AA.substR (Rel.symm AA.compat₂)
  have pow_lift {x y : ℕ} {z : ℤ} : z ≃ x - y → p^x / p^y ≃ p^z := by
    intro (_ : z ≃ x - y)
    calc
      _ = p^x / p^y     := rfl
      _ ≃ p^((x:ℤ) - y) := eqv_symm pow_diff
      _ ≃ p^z           := pow_substR (Rel.symm ‹z ≃ x - y›)
  calc
    _ = p^(a + b)                         := rfl
    _ ≃ p^(((n + k : ℕ):ℤ) - (m + j : ℕ)) := pow_substR ‹a+b ≃ (n+k:ℕ)-(m+j:ℕ)›
    _ ≃ p^(n + k) / p^(m + j)             := pow_diff
    _ ≃ (p^n * p^k) / p^(m + j)           := div_substL Natural.pow_compatL_add
    _ ≃ (p^n * p^k) / (p^m * p^j)         := div_substR Natural.pow_compatL_add
    _ ≃ (p^n / p^m) * (p^k / p^j)         := Rel.symm div_mul_swap
    _ ≃ p^a * (p^k / p^j)                 := mul_substL (pow_lift ‹a ≃ n - m›)
    _ ≃ p^a * p^b                         := mul_substR (pow_lift ‹b ≃ k - j›)

/--
Powers of powers flatten into a single power whose exponent is the product of
the original exponents.

**Property intuition**: First, `p^a` is `a` repetitions of the base (either
directly or as a reciprocal, if `a` is negative). So `(p^a)^b` is `b`
repetitions _of_ an expression that's `a` repetitions of the base, giving
`a * b` repetitions total.

**Proof intuition**: Write both integer exponents as differences of natural
numbers. Use `pow_diff` to simplify the expression to one involving powers of
powers of _natural_ numbers. Use natural number exponent properties, and
`pow_diff` again, to factor out the base and combine exponents until the
expression has a single instance of the base raised to a single exponent.
Simplify that exponent to obtain the result.
-/
theorem pow_flatten {p : ℚ} [AP (p ≄ 0)] {a b : ℤ} : (p^a)^b ≃ p^(a * b) := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (a_eqv : a ≃ n - m)) :=
    Integer.as_diff a
  have Exists.intro (k : ℕ) (Exists.intro (j : ℕ) (b_eqv : b ≃ k - j)) :=
    Integer.as_diff b

  have pow_expand : (p^a)^b ≃ ((p^n)^k/(p^m)^k) / ((p^n)^j/(p^m)^j) := calc
    _ = (p^a)^b                               := rfl
    _ ≃ (p^((n:ℤ)-m))^b                       := pow_substL (pow_substR a_eqv)
    _ ≃ (p^n/p^m)^b                           := pow_substL pow_diff
    _ ≃ (p^n/p^m)^((k:ℤ)-j)                   := pow_substR b_eqv
    _ ≃ (p^n/p^m)^k / (p^n/p^m)^j             := pow_diff
    _ ≃ ((p^n)^k/(p^m)^k) / (p^n/p^m)^j       := div_substL pow_distribR_div
    _ ≃ ((p^n)^k/(p^m)^k) / ((p^n)^j/(p^m)^j) := div_substR pow_distribR_div
  have pow_combine {w x y z : ℕ} : (p^w)^x*(p^y)^z ≃ p^(w*x + y*z) := calc
    _ = (p^w)^x*(p^y)^z := rfl
    _ ≃ p^(w*x)*(p^y)^z := mul_substL Natural.pow_flatten
    _ ≃ p^(w*x)*p^(y*z) := mul_substR Natural.pow_flatten
    _ ≃ p^(w*x + y*z)   := Rel.symm Natural.pow_compatL_add
  have multi_compat {w x y z : ℕ} : ((w*x + y*z : ℕ):ℤ) ≃ (w:ℤ)*x + y*z := calc
    _ = ((w*x + y*z : ℕ):ℤ)           := rfl
    _ ≃ ((w*x : ℕ):ℤ) + ((y*z : ℕ):ℤ) := AA.compat₂
    _ ≃ (w:ℤ)*x + ((y*z : ℕ):ℤ)       := AA.substL AA.compat₂
    _ ≃ (w:ℤ)*x + y*z                 := AA.substR AA.compat₂
  have diff_expand
      {w x y z : ℤ} : (w-x) * (y-z) ≃ (w*y + x*z) - (x*y + w*z)
      := by
    let wy := w*y; let wz := w*z; let xy := x*y; let xz := x*z
    calc
      _ = (w-x) * (y-z)           := rfl
      _ ≃ w * (y-z) - x * (y-z)   := AA.distribR
      _ ≃ (wy - wz) - x * (y-z)   := AA.substL AA.distribL
      _ ≃ (wy - wz) - (xy - xz)   := AA.substR AA.distribL
      _ ≃ (wy - wz) + -(xy - xz)  := Integer.sub_defn
      _ ≃ (wy - wz) + (xz - xy)   := AA.substR Integer.sub_neg_flip
      _ ≃ (wy + -wz) + (xz - xy)  := AA.substL Integer.sub_defn
      _ ≃ (wy + -wz) + (xz + -xy) := AA.substR Integer.sub_defn
      _ ≃ (wy + xz) + (-wz + -xy) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ (wy + xz) + (-xy + -wz) := AA.substR AA.comm
      _ ≃ (wy + xz) + -(xy + wz)  := AA.substR (Rel.symm Integer.neg_compat_add)
      _ ≃ (wy + xz) - (xy + wz)   := Rel.symm Integer.sub_defn
  have pow_reduce : ((n*k + m*j : ℕ):ℤ) - ((m*k + n*j : ℕ):ℤ) ≃ a * b := calc
    _ = ((n*k + m*j : ℕ):ℤ) - ((m*k + n*j : ℕ):ℤ) := rfl
    _ ≃ ((n:ℤ)*k + m*j) - ((m*k + n*j : ℕ):ℤ)     := AA.substL multi_compat
    _ ≃ ((n:ℤ)*k + m*j) - (m*k + n*j)             := AA.substR multi_compat
    _ ≃ ((n:ℤ) - m) * (k - j)                     := Rel.symm diff_expand
    _ ≃ a * (k - j)                               := AA.substL (Rel.symm a_eqv)
    _ ≃ a * b                                     := AA.substR (Rel.symm b_eqv)
  calc
    _ = (p^a)^b                                       := rfl
    _ ≃ ((p^n)^k/(p^m)^k) / ((p^n)^j/(p^m)^j)         := pow_expand
    _ ≃ ((p^n)^k*(p^m)^j) / ((p^m)^k*(p^n)^j)         := div_div_div
    _ ≃ p^(n*k + m*j) / ((p^m)^k*(p^n)^j)             := div_substL pow_combine
    _ ≃ p^(n*k + m*j) / p^(m*k + n*j)                 := div_substR pow_combine
    _ ≃ p^(((n*k + m*j : ℕ):ℤ) - ((m*k + n*j : ℕ):ℤ)) := eqv_symm pow_diff
    _ ≃ p^(a * b)                                     := pow_substR pow_reduce

/--
Integer exponents distribute over multiplication.

**Property intuition**: Multiplication is commutative, so there should be no
difference between repeated multiplication of a product (or its reciprocal, for
negative exponents) and repeated multiplication of its first term, followed by
repeated multiplication of its second term.

**Proof intuition**: Write the integer exponent as a difference of natural
numbers. Convert the expression to a ratio of natural number powers via
`pow_diff`. Invoke the analogous property for natural number exponents, and
factor the result into a product of fractions. Run `pow_diff` in reverse and
convert back to integer exponents to obtain the goal.
-/
theorem pow_distribR_mul
    {p q : ℚ} [AP (p ≄ 0)] [AP (q ≄ 0)] {a : ℤ} : (p * q)^a ≃ p^a * q^a
    := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (a_eqv : a ≃ n - m)) :=
    Integer.as_diff a

  calc
    _ = (p * q)^a                 := rfl
    _ ≃ (p * q)^((n:ℤ)-m)         := pow_substR a_eqv
    _ ≃ (p * q)^n / (p * q)^m     := pow_diff
    _ ≃ (p^n * q^n) / (p * q)^m   := div_substL Natural.pow_distribR_mul
    _ ≃ (p^n * q^n) / (p^m * q^m) := div_substR Natural.pow_distribR_mul
    _ ≃ (p^n / p^m) * (q^n / q^m) := eqv_symm div_mul_swap
    _ ≃ p^((n:ℤ)-m) * (q^n / q^m) := mul_substL (eqv_symm pow_diff)
    _ ≃ p^((n:ℤ)-m) * q^((n:ℤ)-m) := mul_substR (eqv_symm pow_diff)
    _ ≃ p^a * q^((n:ℤ)-m)         := mul_substL (pow_substR (Rel.symm a_eqv))
    _ ≃ p^a * q^a                 := mul_substR (pow_substR (Rel.symm a_eqv))

/-- TODO -/
theorem pow_preserves_pos_base {p : ℚ} [AP (p > 0)] {a : ℤ} : p^a > 0 := by
  have : p > 0 := ‹AP (p > 0)›.ev
  have : sgn p ≃ 1 := gt_zero_sgn.mp ‹p > 0›
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a

  have : sgn (p^a) ≃ 1 := calc
    _ = sgn (p^a)             := rfl
    _ ≃ sgn (p^((n:ℤ) - m))   := sgn_subst (pow_substR ‹a ≃ n - m›)
    _ ≃ sgn (p^n / p^m)       := sgn_subst pow_diff
    _ ≃ sgn (p^n) * sgn (p^m) := sgn_div
    _ ≃ (sgn p)^n * sgn (p^m) := AA.substL sgn_pow
    _ ≃ (sgn p)^n * (sgn p)^m := AA.substR sgn_pow
    _ ≃ (sgn p)^(n + m)       := Rel.symm Natural.pow_compatL_add
    _ ≃ 1^(n + m)             := Natural.pow_substL ‹sgn p ≃ 1›
    _ ≃ 1                     := Natural.pow_absorbL
  have : p^a > 0 := gt_zero_sgn.mpr this
  exact this

theorem pow_order_smth
    {p q : ℚ} {a : ℤ} (p_gt_q : p > q) (q_pos : q > 0)
    : have : AP (p > 0) := AP.mk (gt_trans ‹p > q› ‹q > 0›)
      have : AP (q > 0) := AP.mk ‹q > 0›
      sgn (p^a - q^a) ≃ sgn a
    := by
  -- TODO: Split up the natural number version(s) of this theorem above
  -- The q > 0 part can be done completely separately
  -- And the p^n > q^n part can depend on it
  -- Then here, use integer trichotomy on a
  -- Prove positive case using natural number result above
  -- Negative case can be shown to transform into the positive case
  admit
-/
end Lean4Axiomatic.Rational
