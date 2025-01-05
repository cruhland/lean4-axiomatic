import Lean4Axiomatic.Rational.FloorCeil

/-! # Generic implementation of rational floor and ceiling, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Logic (AP)
open Signed (Positive)

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]
  [Subtraction ℚ] [Order ℚ] [Reciprocation ℚ] [Division ℚ] [Induction.{1} ℚ]

/-- The greatest integer less than or equivalent to the given value. -/
def _floor (p : ℚ) : ℤ :=
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) _) := as_ratio p
  (Integer.divide a b).quotient

/-- The least integer greater than or equivalent to the given value. -/
def _ceil (p : ℚ) : ℤ := sorry

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

/--
Evidence that a rational number can be written as a ratio, with an integer
numerator over a positive integer denominator.
-/
structure AsHalfPosRatio (p : ℚ) where
  numerator : ℤ
  denominator : ℤ
  denominator_gt_zero : denominator > 0
  denominator_neqv_zero : AP (denominator ≄ 0) :=
    have : Positive denominator := Integer.gt_zero_iff_pos.mp ‹denominator > 0›
    AP.mk (Integer.neqv_zero_from_positive ‹Positive denominator›)
  eqv : p ≃ numerator / denominator

/--
Any rational can be written as an integer ratio with positive denominator.
-/
def as_half_pos_ratio (p : ℚ) : AsHalfPosRatio p := sorry

/-- A rational is no smaller than its floor. -/
theorem floor_ub {p : ℚ} : floor p ≤ p := by
  -- We want a positive denominator to avoid reversing the main inequality
  have (AsHalfPosRatio.mk (a:ℤ) (b:ℤ) (_ : b > 0) (_ : AP (b ≄ 0)) p_eqv) :=
    as_half_pos_ratio p
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
    le_substN_div_pos ‹(b:ℚ) > 0› (le_respects_from_integer.mp ‹b * q ≤ a›)

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
  have (AsRatio.mk (a : ℤ) (b : ℤ) (_ : AP (b ≄ 0)) p_eqv) := as_ratio p
  have : p ≃ a/b := p_eqv
  let d := Integer.divide a b
  have : (c:ℚ) < d.quotient + 1 := calc
    _ = (c:ℚ) := rfl
    _ ≤ p := ‹c ≤ p›
    _ ≃ a/b := ‹p ≃ a/b›
    _ ≃ (b * d.quotient + d.remainder)/b := sorry
    _ < ((b * d.quotient + b : ℤ):ℚ)/b := sorry
    _ ≃ (b * (d.quotient + 1))/b := sorry
    _ ≃ ((b:ℚ)/b) * (d.quotient + 1) := sorry
    _ ≃ 1 * (d.quotient + 1) := sorry
    _ ≃ d.quotient + 1 := sorry
  calc
    _ = c := rfl
    _ ≤ d.quotient := sorry
    _ ≃ floor ((a:ℚ)/b) := sorry
    _ ≃ floor p := sorry

/-- A rational is no larger than its ceiling. -/
theorem ceil_lb {p : ℚ} : p ≤ ceil p := sorry

/--
A rational's ceiling is the least integer not less than the rational itself.
-/
theorem ceil_ub {p : ℚ} {a : ℤ} : p ≤ a → ceil p ≤ a := sorry

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
