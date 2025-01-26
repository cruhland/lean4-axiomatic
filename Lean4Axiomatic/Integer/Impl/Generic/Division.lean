import Lean4Axiomatic.Integer.Division

/-! # Generic implementation of integer division functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Lean4Axiomatic.Metric (abs)
open Logic (AP Either)
open Signed (Positive)

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ]

structure DivisionResult (α : Type) where
  quotient : α
  remainder : α

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

variable [Metric ℤ]

/-- Direct translation of natural number division to integers. -/
def basic_divide {a b : ℤ} : a ≥ 0 → b > 0 → EuclideanDivision a b := by
  intro (_ : a ≥ 0) (_ : b > 0)
  show EuclideanDivision a b

  let an : { n : ℕ // a ≃ n } := nonneg_to_natural ‹a ≥ 0›
  let n := an.val
  have : a ≃ n := an.property

  let bn : { m : ℕ // b ≃ m ∧ m > 0 } := pos_to_natural ‹b > 0›
  let m := bn.val
  have : b ≃ m := bn.property.left
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (neqv_zero_from_gt_zero ‹m > 0›)

  let d := nat_divide n m; let q := d.quotient; let r := d.remainder
  have : n ≃ m * q + r := nat_divide_eqv

  have : a ≃ b * (q:ℤ) + (r:ℤ) := calc
    _ = a                       := rfl
    _ ≃ (n:ℤ)                   := ‹a ≃ n›
    _ ≃ ((m * q + r : ℕ):ℤ)     := AA.subst₁ ‹n ≃ m * q + r›
    _ ≃ ((m * q : ℕ):ℤ) + (r:ℤ) := AA.compat₂
    _ ≃ (m:ℤ) * (q:ℤ) + (r:ℤ)   := AA.substL AA.compat₂
    _ ≃ b * (q:ℤ) + (r:ℤ)       := AA.substL (AA.substL (Rel.symm ‹b ≃ m›))

  have : r ≥ 0 := Natural.ge_zero
  have : (r:ℤ) ≥ 0 := from_natural_respects_le.mp ‹r ≥ 0›
  have : r < m := nat_remainder_ub
  have : b ≥ 0 := ge_split.mpr (Or.inl ‹b > 0›)
  have : (r:ℤ) < abs b := calc
    _ = (r:ℤ) := rfl
    _ < (m:ℤ) := from_natural_respects_lt.mp ‹r < m›
    _ ≃ b     := Rel.symm ‹b ≃ m›
    _ ≃ abs b := Rel.symm (abs_ident ‹b ≥ 0›)

  exact show EuclideanDivision a b from {
    quotient := (q:ℤ)
    remainder := (r:ℤ)
    div_eqv := ‹a ≃ b * (q:ℤ) + (r:ℤ)›
    rem_lb := ‹(r:ℤ) ≥ 0›
    rem_ub := ‹(r:ℤ) < abs b›
  }

def nonneg_divide
    {a : ℤ} (a_nonneg : a ≥ 0) (b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b
    :=
  let b' := b * sgn b
  have : Nonzero b := nonzero_iff_neqv_zero.mpr ‹AP (b ≄ 0)›.ev
  have : Positive b' := positive_mul_sgn_self ‹Nonzero b›
  have : b' > 0 := gt_zero_iff_pos.mpr ‹Positive b'›
  let division' : EuclideanDivision a b' := basic_divide ‹a ≥ 0› ‹b' > 0›
  let q := division'.quotient
  let r := division'.remainder

  have : a ≃ b * (sgn b * q) + r := calc
    _ = a                   := rfl
    _ ≃ b' * q + r          := division'.div_eqv
    _ = (b * sgn b) * q + r := rfl
    _ ≃ b * (sgn b * q) + r := AA.substL AA.assoc
  have : r ≥ 0 := division'.rem_lb
  have : b' ≥ 0 := ge_split.mpr (Or.inl ‹b' > 0›)
  have : r < abs b := calc
    _ = r         := rfl
    _ < abs b'    := division'.rem_ub
    _ ≃ b'        := abs_ident ‹b' ≥ 0›
    _ = b * sgn b := rfl
    _ ≃ abs b     := Rel.symm abs_sgn

  show EuclideanDivision a b from {
    quotient := sgn b * q
    remainder := r
    div_eqv := ‹a ≃ b * (sgn b * q) + r›
    rem_lb := ‹r ≥ 0›
    rem_ub := ‹r < abs b›
  }

/-- Definition of division -/
def divide (a b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b :=
  match show Either (a ≥ 0) (-a ≥ 0) from either_nonneg with
  | .inl (_ : a ≥ 0) =>
    show EuclideanDivision a b from nonneg_divide ‹a ≥ 0› b
  | .inr (_ : -a ≥ 0) =>
    let d' : EuclideanDivision (-a) b := nonneg_divide ‹-a ≥ 0› b
    let q' := d'.quotient
    let r' := d'.remainder
    have : a ≃ b * -q' + -r' := calc
      _ = a               := rfl
      _ ≃ -(-a)           := Rel.symm neg_involutive
      _ ≃ -(b * q' + r')  := AA.subst₁ d'.div_eqv
      _ ≃ -(b * q') + -r' := neg_compat_add
      _ ≃ b * -q' + -r'   := AA.substL AA.scompatR
    have : r' ≥ 0 := d'.rem_lb

    match show Either (r' > 0) (r' ≃ 0) from ge_split_either ‹r' ≥ 0› with
    | .inl (_ : r' > 0) =>
      -- Minor lemmas needed to keep the proof of `a ≃ b * q + r` within margin
      have split {x y z : ℤ} : x + y ≃ (x + -z) + (z + y) := calc
        _ = x + y              := rfl
        _ ≃ (x + 0) + y        := AA.substL (Rel.symm AA.identR)
        _ ≃ (x + (-z + z)) + y := AA.substL (AA.substR (Rel.symm AA.inverseL))
        _ ≃ ((x + -z) + z) + y := AA.substL (Rel.symm AA.assoc)
        _ ≃ (x + -z) + (z + y) := AA.assoc
      have factor {x y : ℤ} : x * -y + -abs x ≃ x * -(y + sgn x) := calc
        _ = x * -y + -abs x       := rfl
        _ ≃ x * -y + -(x * sgn x) := AA.substR (AA.subst₁ abs_sgn)
        _ ≃ x * -y + x * -sgn x   := AA.substR AA.scompatR
        _ ≃ x * (-y + -sgn x)     := Rel.symm AA.distribL
        _ ≃ x * -(y + sgn x)      := AA.substR (Rel.symm neg_compat_add)

      /-
      Define or prove all fields of the result structure.

      Although `a ≃ b * -q' + -r'`, we can't have a remainder of `-r'` because
      it's negative. Find an equivalent positive remainder and adjust the
      quotient to compensate.
      -/
      let q := -(q' + sgn b)
      let r := abs b - r'
      have : a ≃ b * q + r := calc
        _ = a                                  := rfl
        _ ≃ b * -q' + -r'                      := ‹a ≃ b * -q' + -r'›
        _ ≃ (b * -q' + -abs b) + (abs b + -r') := split
        _ ≃ (b * -q' + -abs b) + (abs b - r')  := AA.substR (Rel.symm sub_defn)
        _ = (b * -q' + -abs b) + r             := rfl
        _ ≃ b * -(q' + sgn b) + r              := AA.substL factor
        _ = b * q + r                          := rfl
      have : r' ≤ abs b := le_split.mpr (Or.inl d'.rem_ub)
      have : r ≥ 0 := calc
        _ = r             := rfl
        _ = abs b - r'    := rfl
        _ ≥ abs b - abs b := le_substR_sub ‹r' ≤ abs b›
        _ ≃ 0             := sub_same
      have : r < abs b := calc
        _ = r          := rfl
        _ = abs b - r' := rfl
        _ < abs b - 0  := lt_substR_sub ‹r' > 0›
        _ ≃ abs b      := sub_identR

      show EuclideanDivision a b from {
        quotient := q
        remainder := r
        div_eqv := ‹a ≃ b * q + r›
        rem_lb := ‹r ≥ 0›
        rem_ub := ‹r < abs b›
      }

    | .inr (_ : r' ≃ 0) =>
      -- Define or prove all fields of the result structure
      let q := -q'
      let r := 0
      have : a ≃ b * q + r := calc
        _ = a             := rfl
        _ ≃ b * -q' + -r' := ‹a ≃ b * -q' + -r'›
        _ = b * q + -r'   := rfl
        _ ≃ b * q + -0    := AA.substR (AA.subst₁ ‹r' ≃ 0›)
        _ ≃ b * q + 0     := AA.substR (Rel.symm (neg_zero.mp Rel.refl))
        _ = b * q + r     := rfl
      have : r ≥ 0 := le_refl
      have : r ≤ abs b := abs_nonneg
      have : abs b ≄ 0 := mt abs_zero.mpr ‹AP (b ≄ 0)›.ev
      have : r ≄ abs b := Rel.symm ‹abs b ≄ 0›
      have : r < abs b := lt_from_le_neqv ‹r ≤ abs b› ‹r ≄ abs b›

      show EuclideanDivision a b from {
        quotient := q
        remainder := r
        div_eqv := ‹a ≃ b * q + r›
        rem_lb := ‹r ≥ 0›
        rem_ub := ‹r < abs b›
      }


def division : Division ℤ := {
  divide := divide
}

end Lean4Axiomatic.Integer.Impl.Generic
