import Lean4Axiomatic.Rational.FloorCeil

/-! # Generic implementation of rational floor and ceiling, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Logic (AP)
open Metric (abs)
open Signed (Positive sgn)

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]
  [Subtraction ℚ] [Order ℚ] [Reciprocation ℚ] [Division ℚ] [Induction.{1} ℚ]

/-- The greatest integer less than or equivalent to the given value. -/
def _floor (p : ℚ) : ℤ :=
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) _) := as_ratio p
  (Integer.divide a b).quotient

/-- The least integer greater than or equivalent to the given value. -/
def _ceil (p : ℚ) : ℤ := -_floor (-p)

local instance floor_ceil_ops : FloorCeil.Ops ℤ ℚ := {
  floor := _floor
  ceil := _ceil
}

/--
Evaluate `floor` in the common case where we know the integer components of the
rational input.
-/
theorem floor_ratio
    {a b : ℤ} [AP (b ≄ 0)] : floor ((a:ℚ)/b) ≃ (Integer.divide a b).quotient
    := by
  admit

/-- `floor` is a legitimate function on rationals; it respects equivalence. -/
theorem floor_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → floor p₁ ≃ floor p₂ := sorry

/-- A positive integer is nonzero. -/
theorem neqv_zero_from_gt_zero {a : ℤ} : a > 0 → a ≄ 0 := by
  intro (_ : a > 0)
  have : Positive a := Integer.gt_zero_iff_pos.mp ‹a > 0›
  have : a ≄ 0 := Integer.neqv_zero_from_positive ‹Positive a›
  exact this

/--
Evidence that a rational number can be written as a ratio of an integer
numerator over a positive integer denominator.
-/
structure AsHalfPosRatio (p : ℚ) where
  numerator : ℤ
  denominator : ℤ
  denominator_gt_zero : denominator > 0
  eqv
    : have : denominator ≄ 0 := neqv_zero_from_gt_zero ‹denominator > 0›
      have : AP (denominator ≄ 0) := AP.mk ‹denominator ≄ 0›
      p ≃ numerator / denominator

/--
Any rational can be written as an integer ratio with positive denominator.
-/
def as_half_pos_ratio (p : ℚ) : AsHalfPosRatio p :=
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) p_eqv) := as_ratio p
  have : p ≃ a/b := p_eqv

  -- Make a positive denominator
  -- ↓ begin key lines ↓
  let a' := a * sgn b
  let b' := b * sgn b
  have : b' > 0 := calc
    _ = b'        := rfl
    _ = b * sgn b := rfl
    _ > 0         := Integer.mul_sgn_self_gt_zero ‹AP (b ≄ 0)›.ev
  -- ↑  end key lines  ↑

  -- Show the new ratio is equivalent to the input value
  have : AP (b' ≄ 0) := AP.mk (neqv_zero_from_gt_zero ‹b' > 0›)
  have : AP (sgn b ≄ 0) := ‹AP (b ≄ 0)›.map (mt Integer.sgn_zero.mpr)
  have mul_compat {a b : ℤ} : (a:ℚ) * (b:ℚ) ≃ (a * b : ℤ) :=
    eqv_symm mul_compat_from_integer
  have : p ≃ a'/b' := calc
    _ = p                               := rfl
    _ ≃ a/b                             := ‹p ≃ a/b›
    _ ≃ ((a:ℚ)/b) * 1                   := eqv_symm mul_identR
    _ ≃ ((a:ℚ)/b) * ((sgn b : ℚ)/sgn b) := mul_substR (eqv_symm div_same)
    _ ≃ (a * sgn b)/(b * sgn b)         := div_mul_swap
    _ ≃ (a * sgn b : ℤ)/(b * sgn b)     := div_substL mul_compat
    _ ≃ (a * sgn b : ℤ)/(b * sgn b : ℤ) := div_substR mul_compat
    _ = (a':ℚ)/b'                       := rfl

  AsHalfPosRatio.mk a' b' ‹b' > 0› ‹p ≃ a'/b'›

/-- A rational is no smaller than its floor. -/
theorem floor_ub {p : ℚ} : floor p ≤ p := by
  -- We want a positive denominator to avoid reversing the main inequality
  have (AsHalfPosRatio.mk (a:ℤ) (b:ℤ) (_ : b > 0) p_eqv) := as_half_pos_ratio p
  have : AP (b ≄ 0) := AP.mk (neqv_zero_from_gt_zero ‹b > 0›)
  have : p ≃ a/b := p_eqv
  have : (b:ℚ) > 0 := lt_respects_from_integer.mp ‹b > 0›

  -- Use integer division properties to set up the main inequality
  let d := Integer.divide a b; let q := d.quotient; let r := d.remainder
  have : b * q ≤ a := calc
    _ = b * q     := rfl
    -- ↓ begin key lines ↓
    _ ≃ b * q + 0 := Rel.symm AA.identR
    _ ≤ b * q + r := Integer.ge_addL.mp Integer.remainder_lb
    -- ↑  end key lines  ↑
    _ ≃ a         := Rel.symm Integer.divide_eqv
  have : ((b * q : ℤ):ℚ)/b ≤ (a:ℚ)/b :=
    le_substN_div_gt_zero ‹(b:ℚ) > 0› (le_respects_from_integer.mp ‹b * q ≤ a›)

  calc
    _ = (floor p : ℚ)     := rfl
    _ ≃ floor ((a:ℚ)/b)   := from_integer_subst (floor_subst ‹p ≃ a/b›)
    _ ≃ q                 := from_integer_subst floor_ratio
    _ ≃ (b * q)/b         := eqv_symm mulL_div_same
    -- ↓ begin key lines ↓
    _ ≃ ((b * q : ℤ):ℚ)/b := div_substL (eqv_symm mul_compat_from_integer)
    _ ≤ (a:ℚ)/b           := ‹((b * q : ℤ):ℚ)/b ≤ (a:ℚ)/b›
    -- ↑  end key lines  ↑
    _ ≃ p                 := eqv_symm ‹p ≃ a/b›

/--
A rational's floor is the greatest integer not greater than the rational
itself.
-/
theorem floor_lb {p : ℚ} {c : ℤ} : c ≤ p → c ≤ floor p := by
  intro (_ : c ≤ p)
  show c ≤ floor p

  -- We want a positive denominator to avoid reversing the main inequality
  have (AsHalfPosRatio.mk (a:ℤ) (b:ℤ) (_ : b > 0) p_eqv) := as_half_pos_ratio p
  have : AP (b ≄ 0) := AP.mk (neqv_zero_from_gt_zero ‹b > 0›)
  have : p ≃ a/b := p_eqv
  have : b ≥ 0 := Integer.le_split.mpr (Or.inl ‹b > 0›)
  have : (b:ℚ) > 0 := lt_respects_from_integer.mp ‹b > 0›

  -- Use integer division properties to set up the main inequality
  let d := Integer.divide a b; let q := d.quotient; let r := d.remainder
  have : a < b * (q + 1) := calc
    _ = a             := rfl
    -- ↓ begin key lines ↓
    _ ≃ b * q + r     := Integer.divide_eqv
    _ < b * q + abs b := AA.substR Integer.remainder_ub
    -- ↑  end key lines  ↑
    _ ≃ b * q + b     := Integer.add_substR (Integer.abs_ident ‹b ≥ 0›)
    _ ≃ b * q + b * 1 := Integer.add_substR (Rel.symm AA.identR)
    _ ≃ b * (q + 1)   := Rel.symm AA.distribL
  have : (a:ℚ) < (b * (q+1) : ℤ) := lt_respects_from_integer.mp ‹a < b * (q+1)›
  have : (a:ℚ)/b < ((b * (q + 1) : ℤ):ℚ)/b :=
    lt_substN_div_gt_zero ‹(b:ℚ) > 0› ‹(a:ℚ) < (b * (q+1) : ℤ)›

  have : (c:ℚ) < (q + 1 : ℤ) := calc
    _ = (c:ℚ)                   := rfl
    _ ≤ p                       := ‹c ≤ p›
    -- ↓ begin key lines ↓
    _ ≃ a/b                     := ‹p ≃ a/b›
    _ < ((b * (q + 1) : ℤ):ℚ)/b := ‹(a:ℚ)/b < ((b * (q + 1) : ℤ):ℚ)/b›
    -- ↑  end key lines  ↑
    _ ≃ (b * (q + 1 : ℤ))/b     := div_substL mul_compat_from_integer
    _ ≃ (q + 1 : ℤ)             := mulL_div_same
  have : c < q + 1 := lt_respects_from_integer.mpr ‹(c:ℚ) < (q + 1 : ℤ)›
  calc
    -- ↓ begin key lines ↓
    _ = c               := rfl
    _ ≤ q               := Integer.le_iff_lt_incR.mpr ‹c < q + 1›
    -- ↑  end key lines  ↑
    _ ≃ floor ((a:ℚ)/b) := Rel.symm floor_ratio
    _ ≃ floor p         := Rel.symm (floor_subst ‹p ≃ a/b›)

/-- A rational is no larger than its ceiling. -/
theorem ceil_lb {p : ℚ} : p ≤ ceil p := by
  -- ↓ begin key lines ↓
  have : floor (-p) ≤ -p := floor_ub
  -- ↑  end key lines  ↑
  calc
    _ = p                 := rfl
    _ ≃ -(-p)             := eqv_symm neg_involutive
    _ ≤ -(floor (-p) : ℤ) := le_subst_neg ‹floor (-p) ≤ -p›
    _ ≃ (-floor (-p) : ℤ) := eqv_symm neg_compat_from_integer
    _ = ceil p            := rfl

/--
A rational's ceiling is the least integer not less than the rational itself.
-/
theorem ceil_ub {p : ℚ} {a : ℤ} : p ≤ a → ceil p ≤ a := by
  intro (_ : p ≤ a)
  show ceil p ≤ a
  have : (-a:ℤ) ≤ -p := calc
    _ = ((-a:ℤ):ℚ) := rfl
    _ ≃ -(a:ℚ)     := neg_compat_from_integer
    _ ≤ -p         := le_subst_neg ‹p ≤ a›
  -- ↓ begin key lines ↓
  have : -a ≤ floor (-p) := floor_lb ‹(-a:ℤ) ≤ -p›
  -- ↑  end key lines  ↑
  calc
    _ = ceil p      := rfl
    _ = -floor (-p) := rfl
    _ ≤ -(-a)       := Integer.le_neg_flip.mp ‹-a ≤ floor (-p)›
    _ ≃ a           := Integer.neg_involutive

def floor_ceil_props : FloorCeil.Props ℚ := {
  floor_ub := floor_ub
  floor_lb := floor_lb
  ceil_lb := ceil_lb
  ceil_ub := ceil_ub
}

def floor_ceil : FloorCeil ℚ := {
  toOps := floor_ceil_ops
  toProps := floor_ceil_props
}

end Lean4Axiomatic.Rational.Impl.Generic
