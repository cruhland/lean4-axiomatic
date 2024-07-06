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
open Lean4Axiomatic.Signed (Positive sgn)

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

/-- TODO -/
theorem from_integer_preserves_gt_zero {a : ℤ} : a > 0 → (a:ℚ) > 0 := by
  intro (_ : a > 0)
  show (a:ℚ) > 0
  have : sgn (a:ℚ) ≃ 1 := calc
    _ = sgn (a:ℚ) := rfl
    _ ≃ sgn a     := sgn_from_integer
    _ ≃ 1         := Integer.gt_zero_sgn.mp ‹a > 0›
  have : (a:ℚ) > 0 := gt_zero_sgn.mpr ‹sgn (a:ℚ) ≃ 1›
  exact this

/-- TODO -/
inductive NonnegRatio (p : ℚ) : Prop :=
| intro
    (a b : ℤ)
    (a_nneg : a ≥ 0)
    (b_pos : b > 0)
    (p_eqv :
      have : AP ((b:ℚ) > 0) := AP.mk (from_integer_preserves_gt_zero ‹b > 0›)
      p ≃ a / b
    )
  : NonnegRatio p

/-- TODO -/
theorem as_nonneg_ratio {p : ℚ} : p ≥ 0 → NonnegRatio p := by
  intro (_ : p ≥ 0)
  show NonnegRatio p
  have (AsRatio.intro (x : ℤ) (y : ℤ) (_ : Integer.Nonzero y) p_eqv) :=
    as_ratio p
  have : p ≃ x/y := p_eqv
  let a := x * sgn y
  let b := y * sgn y

  have : sgn a ≥ 0 := calc
    _ = sgn a               := rfl
    _ = sgn (x * sgn y)     := rfl
    _ ≃ sgn x * sgn (sgn y) := Integer.sgn_compat_mul
    _ ≃ sgn x * sgn y       := AA.substR Integer.sgn_idemp
    _ ≃ sgn ((x:ℚ)/y)       := Rel.symm sgn_div_integers
    _ ≃ sgn p               := sgn_subst (eqv_symm ‹p ≃ x/y›)
    _ ≥ 0                   := sgn_preserves_ge_zero.mp ‹p ≥ 0›
  have : a ≥ 0 := Integer.sgn_preserves_ge_zero.mpr ‹sgn a ≥ 0›

  have : Integer.Sqrt1 (sgn y) := Integer.sgn_nonzero.mp ‹Integer.Nonzero y›
  have : sgn b ≃ 1 := calc
    _ = sgn b               := rfl
    _ = sgn (y * sgn y)     := rfl
    _ ≃ sgn y * sgn (sgn y) := Integer.sgn_compat_mul
    _ ≃ sgn y * sgn y       := AA.substR Integer.sgn_idemp
    _ ≃ 1                   := ‹Integer.Sqrt1 (sgn y)›.elim
  have : b > 0 := Integer.gt_zero_sgn.mpr ‹sgn b ≃ 1›

  have a_liftQ : (x:ℚ) * sgn y ≃ (a:ℚ) := calc
    _ = (x:ℚ) * sgn y       := rfl
    _ ≃ ((x * sgn y : ℤ):ℚ) := eqv_symm mul_compat_from_integer
    _ ≃ (a:ℚ)               := from_integer_subst Rel.refl
  have b_liftQ : (y:ℚ) * sgn y ≃ (b:ℚ) := calc
    _ = (y:ℚ) * sgn y       := rfl
    _ ≃ ((y * sgn y : ℤ):ℚ) := eqv_symm mul_compat_from_integer
    _ ≃ (b:ℚ)               := from_integer_subst Rel.refl
  have : AP ((b:ℚ) > 0) := AP.mk (from_integer_preserves_gt_zero ‹b > 0›)
  have : p ≃ a/b := calc
    _ = p                                   := rfl
    _ ≃ x/y                                 := ‹p ≃ x/y›
    _ ≃ ((x:ℚ)/y) * 1                       := eqv_symm mul_identR
    _ ≃ ((x:ℚ)/y) * (((sgn y:ℤ):ℚ)/(sgn y)) := mul_substR (eqv_symm div_same)
    _ ≃ ((x:ℚ) * sgn y)/(y * sgn y)         := div_mul_swap
    _ ≃ (a:ℚ)/(y * sgn y)                   := div_substL a_liftQ
    _ ≃ (a:ℚ)/b                             := div_substR b_liftQ

  have : NonnegRatio p := NonnegRatio.intro a b ‹a ≥ 0› ‹b > 0› ‹p ≃ a/b›
  exact this

/-- TODO -/
theorem sgn_diff_pow_pos
    {p q : ℚ} {n : ℕ} : p ≥ 0 → q ≥ 0 → n > 0 → sgn (p^n - q^n) ≃ sgn (p - q)
    := by
  intro (_ : p ≥ 0) (_ : q ≥ 0) (_ : n > 0)
  show sgn (p^n - q^n) ≃ sgn (p - q)
  have (NonnegRatio.intro (a : ℤ) (b : ℤ) (_ : a ≥ 0) (_ : b > 0) p_eqv) :=
    as_nonneg_ratio ‹p ≥ 0›
  have : AP ((b:ℚ) > 0) := AP.mk (from_integer_preserves_gt_zero ‹b > 0›)
  have : p ≃ a/b := p_eqv
  have (NonnegRatio.intro (c : ℤ) (d : ℤ) (_ : c ≥ 0) (_ : d > 0) q_eqv) :=
    as_nonneg_ratio ‹q ≥ 0›
  have : AP ((d:ℚ) > 0) := AP.mk (from_integer_preserves_gt_zero ‹d > 0›)
  have : q ≃ c/d := q_eqv

  have sgn_mul_absorbL {x y : ℤ} : x > 0 → sgn (x * y) ≃ sgn y := by
    intro (_ : x > 0)
    show sgn (x * y) ≃ sgn y
    calc
      _ = sgn (x * y)   := rfl
      _ ≃ sgn x * sgn y := Integer.sgn_compat_mul
      _ ≃ 1 * sgn y     := AA.substL (Integer.gt_zero_sgn.mp ‹x > 0›)
      _ ≃ sgn y         := AA.identL
  have : sgn (b * d) ≃ 1 := calc
    _ = sgn (b * d)   := rfl
    _ ≃ sgn d         := sgn_mul_absorbL ‹b > 0›
    _ ≃ 1             := Integer.gt_zero_sgn.mp ‹d > 0›
  have : b * d > 0 := Integer.gt_zero_sgn.mpr ‹sgn (b * d) ≃ 1›
  have : b * d ≥ 0 := Integer.ge_split.mpr (Or.inl ‹b * d > 0›)
  have sgn_bd_pow {k : ℕ} : sgn ((b * d)^k) ≃ 1 := calc
    _ = sgn ((b * d)^k) := rfl
    _ ≃ (sgn (b * d))^k := Integer.sgn_pow
    _ ≃ 1^k             := Natural.pow_substL ‹sgn (b * d) ≃ 1›
    _ ≃ 1               := Natural.pow_absorbL
  have : Integer.Sqrt1 (sgn (b * d)) :=
    Integer.sqrt1_cases.mpr (Or.inl ‹sgn (b * d) ≃ 1›)
  have : Integer.Nonzero (b * d) := Integer.sgn_nonzero.mpr this
  have sqrt1_sgn_bd_pow {k : ℕ} : Integer.Sqrt1 (sgn ((b * d)^k)) :=
    Integer.sqrt1_cases.mpr (Or.inl sgn_bd_pow)
  have nonzero_bd_pow {k : ℕ} : Integer.Nonzero ((b * d)^k) :=
    Integer.sgn_nonzero.mpr sqrt1_sgn_bd_pow
  have : sgn (b * c) ≥ 0 := calc
    _ = sgn (b * c)   := rfl
    _ ≃ sgn c         := sgn_mul_absorbL ‹b > 0›
    _ ≥ 0             := Integer.sgn_preserves_ge_zero.mp ‹c ≥ 0›
  have : b * c ≥ 0 := Integer.sgn_preserves_ge_zero.mpr this
  have : d ≥ 0 := Integer.ge_split.mpr (Or.inl ‹d > 0›)
  have : a * d ≥ 0 := Integer.mul_preserves_nonneg ‹a ≥ 0› ‹d ≥ 0›

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
      {k : ℕ}
      : (a:ℚ)^k * (d:ℚ)^k - (b:ℚ)^k * (c:ℚ)^k ≃ (((a * d)^k - (b * c)^k : ℤ):ℚ)
      := calc
    _ = (a:ℚ)^k * (d:ℚ)^k - (b:ℚ)^k * (c:ℚ)^k     := rfl
    _ ≃ (((a * d)^k : ℤ):ℚ) - (b:ℚ)^k * (c:ℚ)^k   := sub_substL mul_pow_liftQ
    _ ≃ (((a * d)^k : ℤ):ℚ) - (((b * c)^k : ℤ):ℚ) := sub_substR mul_pow_liftQ
    _ ≃ (((a * d)^k - (b * c)^k : ℤ):ℚ)           := sub_liftQ
  have sub_pow_expand {k : ℕ} : p^k - q^k ≃ (a:ℚ)^k/b^k - (c:ℚ)^k/d^k := calc
    _ = p^k - q^k                 := rfl
    _ ≃ ((a:ℚ)/b)^k - q^k         := sub_substL (Natural.pow_substL ‹p ≃ a/b›)
    _ ≃ ((a:ℚ)/b)^k - ((c:ℚ)/d)^k := sub_substR (Natural.pow_substL ‹q ≃ c/d›)
    _ ≃ (a:ℚ)^k/b^k - ((c:ℚ)/d)^k := sub_substL pow_distribR_div
    _ ≃ (a:ℚ)^k/b^k - (c:ℚ)^k/d^k := sub_substR pow_distribR_div
  have sub_pow_frac
      {k : ℕ}
      : have : Integer.Nonzero ((b * d)^k) := nonzero_bd_pow
        p^k - q^k ≃ (((a * d)^k - (b * c)^k : ℤ):ℚ)/(((b * d)^k : ℤ):ℚ)
      := by
    have : Integer.Nonzero ((b * d)^k) := nonzero_bd_pow
    calc
    _ = p^k - q^k                                   := rfl
    _ ≃ (a:ℚ)^k/b^k - (c:ℚ)^k/d^k                   := sub_pow_expand
    _ ≃ ((a:ℚ)^k*(d:ℚ)^k - (b:ℚ)^k*(c:ℚ)^k)/((b:ℚ)^k*(d:ℚ)^k) := sub_fractions
    _ ≃ (((a*d)^k-(b*c)^k:ℤ):ℚ)/((b:ℚ)^k * (d:ℚ)^k) := div_substL sub_mul_liftQ
    _ ≃ (((a*d)^k-(b*c)^k:ℤ):ℚ)/(((b*d)^k:ℤ):ℚ)     := div_substR mul_pow_liftQ

  have sgn_sub_pow_factor
      : sgn (p^n - q^n) ≃ sgn ((a*d)^n-(b*c)^n) * sgn ((b*d)^n)
      := calc
    _ = sgn (p^n - q^n)                               := rfl
    _ ≃ sgn ((((a*d)^n-(b*c)^n:ℤ):ℚ)/(((b*d)^n:ℤ):ℚ)) := sgn_subst sub_pow_frac
    _ ≃ sgn ((a*d)^n-(b*c)^n) * sgn ((b*d)^n)         := sgn_div_integers
  have sgn_diff_int_pow : sgn ((a * d)^n - (b * c)^n) ≃ sgn (a * d - b * c) :=
    Integer.sgn_diff_pow_pos ‹a * d ≥ 0› ‹b * c ≥ 0› ‹n > 0›
  have sgn_bd_drop_pow : sgn ((b * d)^n) ≃ sgn (b * d) := calc
    _ = sgn ((b * d)^n) := rfl
    _ ≃ (sgn (b * d))^n := Integer.sgn_pow
    _ ≃ sgn (b * d)     := Integer.sgn_absorb_pow ‹b * d ≥ 0› ‹n > 0›

  have drop_pow_ones_ℚ : p^1 - q^1 ≃ p - q := calc
    _ = p^1 - q^1 := rfl
    _ ≃ p - q^1   := sub_substL Natural.pow_one
    _ ≃ p - q     := sub_substR Natural.pow_one
  have drop_pow_num {x y : ℤ} : ((x^1 - y^1 : ℤ):ℚ) ≃ ((x - y : ℤ):ℚ) := calc
    _ = ((x^1 - y^1 : ℤ):ℚ) := rfl
    _ ≃ ((x - y^1 : ℤ):ℚ)   := from_integer_subst (AA.substL Natural.pow_one)
    _ ≃ ((x - y : ℤ):ℚ)     := from_integer_subst (AA.substR Natural.pow_one)
  have drop_pow_den {x : ℤ} : ((x^1:ℤ):ℚ) ≃ (x:ℚ) :=
    from_integer_subst Natural.pow_one
  have sub_frac : p - q ≃ ((a * d - b * c : ℤ):ℚ)/((b * d : ℤ):ℚ) := calc
    _ = p - q                                       := rfl
    _ ≃ p^1 - q^1                                   := eqv_symm drop_pow_ones_ℚ
    _ ≃ (((a*d)^1 - (b*c)^1 : ℤ):ℚ)/(((b*d)^1:ℤ):ℚ) := sub_pow_frac
    _ ≃ ((a*d - b*c : ℤ):ℚ)/(((b*d)^1:ℤ):ℚ)         := div_substL drop_pow_num
    _ ≃ ((a*d - b*c : ℤ):ℚ)/((b*d:ℤ):ℚ)             := div_substR drop_pow_den

  calc
    _ = sgn (p^n - q^n)                       := rfl
    _ ≃ sgn ((a*d)^n-(b*c)^n) * sgn ((b*d)^n) := sgn_sub_pow_factor
    _ ≃ sgn (a*d - b*c) * sgn ((b*d)^n)       := AA.substL sgn_diff_int_pow
    _ ≃ sgn (a*d - b*c) * sgn (b*d)           := AA.substR sgn_bd_drop_pow
    _ ≃ sgn (((a*d - b*c:ℤ):ℚ)/((b*d:ℤ):ℚ))   := Rel.symm sgn_div_integers
    _ ≃ sgn (p - q)                           := sgn_subst (eqv_symm sub_frac)

/-- TODO -/
theorem pow_pos_preserves_gt_nonneg
    {p q : ℚ} {n : ℕ} : n > 0 → q ≥ 0 → p > q → p^n > q^n
    := by
  intro (_ : n > 0) (_ : q ≥ 0) (_ : p > q)
  show p^n > q^n
  have : p ≥ q := ge_cases.mpr (Or.inl ‹p > q›)
  have : p ≥ 0 := ge_trans ‹p ≥ q› ‹q ≥ 0›
  have : sgn (p^n - q^n) ≃ 1 := calc
    _ = sgn (p^n - q^n) := rfl
    _ ≃ sgn (p - q)     := sgn_diff_pow_pos ‹p ≥ 0› ‹q ≥ 0› ‹n > 0›
    _ ≃ 1               := gt_sgn.mp ‹p > q›
  have : p^n > q^n := gt_sgn.mpr ‹sgn (p^n - q^n) ≃ 1›
  exact this

/-- TODO -/
theorem pow_preserves_ge_nonneg
    {p q : ℚ} {n : ℕ} : q ≥ 0 → p ≥ q → p^n ≥ q^n
    := by
  intro (_ : q ≥ 0) (_ : p ≥ q)
  show p^n ≥ q^n
  have : n ≥ 0 := Natural.ge_zero
  have : n > 0 ∨ n ≃ 0 := Natural.ge_split ‹n ≥ 0›
  match ‹n > 0 ∨ n ≃ 0› with
  | Or.inl (_ : n > 0) =>
    have : p ≥ 0 := ge_trans ‹p ≥ q› ‹q ≥ 0›
    have : sgn (p^n - q^n) ≥ 0 := calc
      _ = sgn (p^n - q^n) := rfl
      _ ≃ sgn (p - q)     := sgn_diff_pow_pos ‹p ≥ 0› ‹q ≥ 0› ‹n > 0›
      _ ≥ 0               := ge_sgn_ge_zero.mp ‹p ≥ q›
    have : p^n ≥ q^n := ge_sgn_ge_zero.mpr ‹sgn (p^n - q^n) ≥ 0›
    exact this
  | Or.inr (_ : n ≃ 0) =>
    have : p^n ≃ q^n := calc
      _ = p^n := rfl
      _ ≃ p^0 := Natural.pow_substR ‹n ≃ 0›
      _ ≃ 1   := Natural.pow_zero
      _ ≃ q^0 := eqv_symm Natural.pow_zero
      _ ≃ q^n := Natural.pow_substR (Rel.symm ‹n ≃ 0›)
    have : p^n ≥ q^n := ge_cases.mpr (Or.inr ‹p^n ≃ q^n›)
    exact this

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

-- TODO: Consider not using this and creating the AP version as needed
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

/-- TODO -/
theorem pow_neg_one {p : ℚ} [AP (p ≄ 0)] : p^(-1:ℤ) ≃ p⁻¹ := calc
  _ = p^(-1:ℤ)    := rfl
  _ = p^(-(1:ℤ))  := rfl
  _ ≃ 1 / p^(1:ℕ) := pow_neg
  _ ≃ 1 / p       := div_substR Natural.pow_one
  _ ≃ p⁻¹         := div_identL

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
theorem pow_preserves_pos_base
    {p : ℚ} {a : ℤ} (p_pos : p > 0)
    : have : AP (p > 0) := AP.mk ‹p > 0›
      p^a > 0
    := by
  have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : a ≃ n - m)) :=
    Integer.as_diff a

  have : AP (p > 0) := AP.mk ‹p > 0›
  have : sgn (p^a) ≃ 1 := calc
    _ = sgn (p^a)             := rfl
    _ ≃ sgn (p^((n:ℤ) - m))   := sgn_subst (pow_substR ‹a ≃ n - m›)
    _ ≃ sgn (p^n / p^m)       := sgn_subst pow_diff
    _ ≃ sgn (p^n) * sgn (p^m) := sgn_div
    _ ≃ (sgn p)^n * sgn (p^m) := AA.substL sgn_pow
    _ ≃ (sgn p)^n * (sgn p)^m := AA.substR sgn_pow
    _ ≃ (sgn p)^(n + m)       := Rel.symm Natural.pow_compatL_add
    _ ≃ 1^(n + m)             := Natural.pow_substL (gt_zero_sgn.mp ‹p > 0›)
    _ ≃ 1                     := Natural.pow_absorbL
  have : p^a > 0 := gt_zero_sgn.mpr this
  exact this

/-- TODO -/
theorem sgn_diff_pow
    {p q : ℚ} {a : ℤ} [p_pos : AP (p > 0)] [q_pos : AP (q > 0)]
    : sgn (p^a - q^a) ≃ sgn (p - q) * sgn a
    := by
  have : p ≥ 0 := ge_cases.mpr (Or.inl ‹AP (p > 0)›.ev)
  have : q ≥ 0 := ge_cases.mpr (Or.inl ‹AP (q > 0)›.ev)
  have (Exists.intro (n : ℕ) (And.intro (_ : n > 0) (_ : a ≃ n * sgn a))) :=
    Integer.as_size_with_sign a
  have : AA.OneOfThree₁ (sgn a ≃ 0) (sgn a ≃ 1) (sgn a ≃ -1) :=
    Integer.sgn_trichotomy a
  match ‹AA.OneOfThree₁ (sgn a ≃ 0) (sgn a ≃ 1) (sgn a ≃ -1)› with
  | AA.OneOfThree₁.first (_ : sgn a ≃ 0) =>
    have pow_a_simp {x : ℚ} [AP (x ≄ 0)] : x^a ≃ 1 := calc
      _ = x^a     := rfl
      _ ≃ x^(0:ℤ) := pow_substR (Integer.sgn_zero.mpr ‹sgn a ≃ 0›)
      _ ≃ x^(0:ℕ) := pow_nonneg
      _ ≃ 1       := Natural.pow_zero
    calc
      _ = sgn (p^a - q^a)     := rfl
      _ ≃ sgn (1 - q^a)       := sgn_subst (sub_substL pow_a_simp)
      _ ≃ sgn ((1:ℚ) - 1)     := sgn_subst (sub_substR pow_a_simp)
      _ ≃ sgn (0:ℚ)           := sgn_subst (sub_eqv_zero_iff_eqv.mpr eqv_refl)
      _ ≃ 0                   := sgn_zero.mp eqv_refl
      _ ≃ sgn (p - q) * 0     := Rel.symm AA.absorbR
      _ ≃ sgn (p - q) * sgn a := AA.substR (Rel.symm ‹sgn a ≃ 0›)
  | AA.OneOfThree₁.second (_ : sgn a ≃ 1) =>
    have pow_a_simp {x : ℚ} [AP (x ≄ 0)] : x^a ≃ x^n := calc
      _ = x^a               := rfl
      _ ≃ x^((n:ℤ) * sgn a) := pow_substR ‹a ≃ n * sgn a›
      _ ≃ x^((n:ℤ) * 1)     := pow_substR (AA.substR ‹sgn a ≃ 1›)
      _ ≃ x^(n:ℤ)           := pow_substR AA.identR
      _ ≃ x^n               := pow_nonneg
    calc
      _ = sgn (p^a - q^a)     := rfl
      _ ≃ sgn (p^n - q^a)     := sgn_subst (sub_substL pow_a_simp)
      _ ≃ sgn (p^n - q^n)     := sgn_subst (sub_substR pow_a_simp)
      _ ≃ sgn (p - q)         := sgn_diff_pow_pos ‹p ≥ 0› ‹q ≥ 0› ‹n > 0›
      _ ≃ sgn (p - q) * 1     := Rel.symm AA.identR
      _ ≃ sgn (p - q) * sgn a := AA.substR (Rel.symm ‹sgn a ≃ 1›)
  | AA.OneOfThree₁.third (_ : sgn a ≃ -1) =>
    have pow_a_simp {x : ℚ} [AP (x ≄ 0)] : x^a ≃ (x^n)⁻¹ := calc
      _ = x^a               := rfl
      _ ≃ x^((n:ℤ) * sgn a) := pow_substR ‹a ≃ n * sgn a›
      _ ≃ x^((n:ℤ) * -1)    := pow_substR (AA.substR ‹sgn a ≃ -1›)
      _ ≃ (x^(n:ℤ))^(-1:ℤ)  := eqv_symm pow_flatten
      _ ≃ (x^(n:ℤ))⁻¹       := pow_neg_one
      _ ≃ (x^n)⁻¹           := recip_subst pow_nonneg
    calc
      _ = sgn (p^a - q^a)         := rfl
      _ ≃ sgn ((p^n)⁻¹ - q^a)     := sgn_subst (sub_substL pow_a_simp)
      _ ≃ sgn ((p^n)⁻¹ - (q^n)⁻¹) := sgn_subst (sub_substR pow_a_simp)
      _ ≃ sgn (q^n - p^n)         := sgn_sub_recip
      _ ≃ sgn (q - p)             := sgn_diff_pow_pos ‹q ≥ 0› ‹p ≥ 0› ‹n > 0›
      _ ≃ sgn (-(p - q))          := sgn_subst (eqv_symm neg_sub)
      _ ≃ -sgn (p - q)            := sgn_compat_neg
      _ ≃ -1 * sgn (p - q)        := Rel.symm Integer.mul_neg_one
      _ ≃ sgn (p - q) * -1        := AA.comm
      _ ≃ sgn (p - q) * sgn a     := AA.substR (Rel.symm ‹sgn a ≃ -1›)

/-- TODO -/
theorem pow_pos_preserves_ge_pos
    {p q : ℚ} {a : ℤ} (q_pos : q > 0) (a_pos : a > 0) (p_ge_q : p ≥ q)
    : have : AP (q > 0) := AP.mk ‹q > 0›
      have : AP (p > 0) := AP.mk (trans ‹p ≥ q› ‹q > 0›)
      p^a ≥ q^a
    := by
  have : AP (q > 0) := AP.mk ‹q > 0›
  have : AP (p > 0) := AP.mk (trans ‹p ≥ q› ‹q > 0›)
  have : sgn (p^a - q^a) ≥ 0 := calc
    _ = sgn (p^a - q^a)     := rfl
    _ ≃ sgn (p - q) * sgn a := sgn_diff_pow
    _ ≃ sgn (p - q) * 1     := AA.substR (Integer.gt_zero_sgn.mp ‹a > 0›)
    _ ≃ sgn (p - q)         := AA.identR
    _ ≥ 0                   := ge_sgn_ge_zero.mp ‹p ≥ q›
  have : p^a ≥ q^a := ge_sgn_ge_zero.mpr ‹sgn (p^a - q^a) ≥ 0›
  exact this

/-- TODO -/
theorem pow_neg_reverses_ge_pos
    {p q : ℚ} {a : ℤ} (q_pos : q > 0) (a_neg : a < 0) (p_ge_q : p ≥ q)
    : have : AP (q > 0) := AP.mk ‹q > 0›
      have : AP (p > 0) := AP.mk (trans ‹p ≥ q› ‹q > 0›)
      p^a ≤ q^a
    := by
  have : AP (q > 0) := AP.mk ‹q > 0›
  have : AP (p > 0) := AP.mk (trans ‹p ≥ q› ‹q > 0›)
  have : sgn (q^a - p^a) ≥ 0 := calc
    _ = sgn (q^a - p^a)     := rfl
    _ ≃ sgn (q - p) * sgn a := sgn_diff_pow
    _ ≃ sgn (q - p) * -1    := AA.substR (Integer.lt_zero_sgn.mp ‹a < 0›)
    _ ≃ -1 * sgn (q - p)    := AA.comm
    _ ≃ -sgn (q - p)        := Integer.mul_neg_one
    _ ≃ sgn (-(q - p))      := Rel.symm sgn_compat_neg
    _ ≃ sgn (p - q)         := sgn_subst neg_sub
    _ ≥ 0                   := ge_sgn_ge_zero.mp ‹p ≥ q›
  have : p^a ≤ q^a := ge_sgn_ge_zero.mpr ‹sgn (q^a - p^a) ≥ 0›
  exact this

end Lean4Axiomatic.Rational
