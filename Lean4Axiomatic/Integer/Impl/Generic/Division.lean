import Lean4Axiomatic.Integer.Division

/-! # Generic implementation of integer division functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Lean4Axiomatic.Metric (abs)
open Logic (AP)
open Signed (Positive)

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ]

def nat_divide (n m : ℕ) [AP (m ≄ 0)] : DivisionResult ℕ := sorry

theorem nat_divide_eqv
    {n m : ℕ} [AP (m ≄ 0)]
    : let d := nat_divide n m; n ≃ m * d.quotient + d.remainder
    := by
  admit

theorem nat_remainder_ub
    {n m : ℕ} [AP (m ≄ 0)] : (nat_divide n m).remainder < m
    := by
  admit

theorem neqv_zero_from_gt_zero {n : ℕ} : n > 0 → n ≄ 0 := by
  intro (_ : n > 0)
  have : Positive n := Natural.lt_zero_pos.mpr ‹n > 0›
  have : n ≄ 0 := Signed.positive_defn.mp ‹Positive n›
  exact this

def nonneg_to_natural {a : ℤ} : a ≥ 0 → { n : ℕ // a ≃ n } := sorry

variable [Subtraction ℤ]

def pos_to_natural {a : ℤ} : a > 0 → { n : ℕ // a ≃ n ∧ n > 0 } := by
  intro (_ : a > 0)
  show { n : ℕ // a ≃ n ∧ n > 0 }

  have : a ≥ 0 := ge_split.mpr (Or.inl ‹a > 0›)
  have (Subtype.mk (n : ℕ) (_ : a ≃ n)) := nonneg_to_natural ‹a ≥ 0›
  have : (n:ℤ) > 0 := calc
    _ = (n:ℤ) := rfl
    _ ≃ a     := Rel.symm ‹a ≃ n›
    _ > 0     := ‹a > 0›
  have : n > 0 := from_natural_respects_lt.mpr ‹(n:ℤ) > 0›
  exact Subtype.mk n (And.intro ‹a ≃ n› ‹n > 0›)

def basic_divide {a b : ℤ} : a ≥ 0 → b > 0 → DivisionResult ℤ := by
  intro (_ : a ≥ 0) (_ : b > 0)
  show DivisionResult ℤ

  let an : { n : ℕ // a ≃ n } := nonneg_to_natural ‹a ≥ 0›
  let n := an.val

  let bn : { m : ℕ // b ≃ m ∧ m > 0 } := pos_to_natural ‹b > 0›
  let m := bn.val
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (neqv_zero_from_gt_zero ‹m > 0›)

  let d := nat_divide n m
  exact DivisionResult.mk (d.quotient:ℤ) (d.remainder:ℤ)

theorem basic_divide_eqv
    {a b : ℤ} (a_nonneg : a ≥ 0) (b_pos : b > 0)
    : let d := basic_divide ‹a ≥ 0› ‹b > 0›; a ≃ b * d.quotient + d.remainder
    := by
  let d := basic_divide ‹a ≥ 0› ‹b > 0›
  let q := d.quotient
  let r := d.remainder
  show a ≃ b * q + r

  -- Find the natural number equivalents of the inputs, with properties
  let an : { n : ℕ // a ≃ n } := nonneg_to_natural ‹a ≥ 0›
  let n := an.val
  have : a ≃ n := an.property

  let bn : { m : ℕ // b ≃ m ∧ m > 0 } := pos_to_natural ‹b > 0›
  let m := bn.val
  have : b ≃ m := bn.property.left
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (neqv_zero_from_gt_zero ‹m > 0›)

  -- Perform natural number division
  let d' := nat_divide n m; let q' := d'.quotient; let r' := d'.remainder
  have : n ≃ m * q' + r' := nat_divide_eqv

  -- Convert the natural number division results to integers
  calc
    _ = a                         := rfl
    _ ≃ (n:ℤ)                     := ‹a ≃ n›
    _ ≃ ((m * q' + r' : ℕ):ℤ)     := AA.subst₁ ‹n ≃ m * q' + r'›
    _ ≃ ((m * q' : ℕ):ℤ) + (r':ℤ) := AA.compat₂
    _ ≃ (m:ℤ) * (q':ℤ) + (r':ℤ)   := AA.substL AA.compat₂
    _ ≃ b * (q':ℤ) + (r':ℤ)       := AA.substL (AA.substL (Rel.symm ‹b ≃ m›))
    _ = b * q + r                 := rfl

theorem basic_remainder_lb
    {a b : ℤ} (a_nonneg : a ≥ 0) (b_pos : b > 0)
    : (basic_divide ‹a ≥ 0› ‹b > 0›).remainder ≥ 0 := by
  -- m ≥ 0 → b ≥ 0
  admit

variable [Metric ℤ]

theorem basic_remainder_ub
    {a b : ℤ} (a_nonneg : a ≥ 0) (b_pos : b > 0)
    : (basic_divide ‹a ≥ 0› ‹b > 0›).remainder < abs b := by
  -- r < m
  -- (r:ℤ) < (m:ℤ) ≃ b ≃ abs b (bc b > 0)
  admit

/-- Definition of division -/
def divide (a b : ℤ) [AP (b ≄ 0)] : DivisionResult ℤ :=
  -- start by making a' := a * sgn b; b' := b * sgn b
  -- this means b' is abs b, and the remainder inequalities from nat div
  -- will directly translate to int div
  -- but if a' is negative we still need to transform it to do nat div
  -- a' = -7; b' := 5
  -- 7 ≃ 5 * 1 + 2
  -- -7 ≃ 5 * (-2) + 3
  -- a ≃ 0, b ≃ 0 => a = b * q + r => 0 = 0 * 0 + 0

  -- a ≃ n * sa
  -- b ≃ m * sb
  -- a / b ≃ (n * sa) / (m * sb) ≃ (n / m) * (sa / sb) ≃ (n / m) * sa * sb
  -- n ≃ m * q + r
  -- r ≃ n - m * q
  -- 0 ≤ r
  -- r < m ↔ sgn (r - m) ≃ -1 ↔ sgn (r - m) * sb ≃ -1 * sb
  -- n * sa ≃ (m * q + r) * sa ≃ m * sa * q + r * sa
  -- a ≃ n * sa ≃ (m * q + r) * sa ≃ (m * q + r) * sa * (sb * sb)
  -- ≃ (m * sb * q + r * sb) * sa * sb ≃ (b * q + r * sb) * sa * sb
  -- ≃ b * (q * sa * sb) + (r * sa)
  --
  sorry

local instance division_ops : Division.Ops ℤ := {
  divide := divide
}

/--
How the `a` in `divide a b` is split between divisor (`b`), quotient, and
remainder.
-/
theorem divide_eqv
    {a b : ℤ} [AP (b ≄ 0)] : let d := a ÷ b; a ≃ b * d.quotient + d.remainder
    := by
  admit

/-- The remainder is always nonnegative. -/
theorem remainder_lb {a b : ℤ} [AP (b ≄ 0)] : (a ÷ b).remainder ≥ 0 := by
  admit

/--
The remainder is always closer to zero than the divisor.

If this were not true, the quotient could be increased by one, and the
magnitude of the divisor subtracted from the remainder to bring it under the
limit.
-/
theorem remainder_ub {a b : ℤ} [AP (b ≄ 0)] : (a ÷ b).remainder < abs b := by
  admit

def division_props : Division.Props ℤ := {
  divide_eqv := divide_eqv
  remainder_lb := remainder_lb
  remainder_ub := remainder_ub
}

def division : Division ℤ := {
  toOps := division_ops
  toProps := division_props
}

end Lean4Axiomatic.Integer.Impl.Generic
