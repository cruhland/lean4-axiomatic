import Lean4Axiomatic.Integer.Division
import Lean4Axiomatic.Integer.Exponentiation

/-! # Generic implementation of integer division functions and properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

open Lean4Axiomatic.Metric (abs)
open Logic (AP Either)
open Signed (Positive)

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ] [Subtraction ℤ] [Metric ℤ]

/-- Integer Euclidean division with a nonnegative dividend. -/
def div_euclidean_nonneg
    {a : ℤ} (a_nonneg : a ≥ 0) (b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b
    :=
  /- Find the natural number equivalent to the nonnegative dividend -/
  let an : { n : ℕ // a ≃ n } := nonneg_to_natural ‹a ≥ 0›
  let n := an.val
  have : a ≃ n := an.property

  /- Find the natural number equivalent to the divisor's absolute value -/
  have : 0 ≤ abs b := abs_nonneg
  have : 0 ≄ abs b := Rel.symm (mt abs_zero.mpr ‹AP (b ≄ 0)›.ev)
  have : abs b > 0 := lt_from_le_neqv ‹0 ≤ abs b› ‹0 ≄ abs b›
  let bn : { m : ℕ // abs b ≃ m ∧ m > 0 } := pos_to_natural ‹abs b > 0›
  let m := bn.val
  have : (m:ℤ) ≃ abs b := Rel.symm bn.property.left
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (Natural.neqv_zero_from_gt_zero ‹m > 0›)

  /- Natural number division and results -/
  let d' := n ÷ m
  let q' := d'.quotient
  let r' := d'.remainder
  have : n ≃ m * q' + r' := d'.div_eqv
  have : r' ≥ 0 := Natural.ge_zero
  have : r' < m := d'.rem_ub

  /- Adjust results to obtain integer division -/
  let q := sgn b * q'
  let r := (r':ℤ)
  have : a ≃ b * q + r := calc
    _ = a                         := rfl
    _ ≃ (n:ℤ)                     := ‹a ≃ n›
    _ ≃ ((m * q' + r' : ℕ):ℤ)     := AA.subst₁ ‹n ≃ m * q' + r'›
    _ ≃ ((m * q' : ℕ):ℤ) + (r':ℤ) := AA.compat₂
    _ ≃ (m:ℤ) * (q':ℤ) + (r':ℤ)   := AA.substL AA.compat₂
    _ = (m:ℤ) * q' + r'           := rfl
    _ ≃ abs b * q' + r'           := AA.substL (AA.substL ‹(m:ℤ) ≃ abs b›)
    _ ≃ (b * sgn b) * q' + r'     := AA.substL (AA.substL abs_sgn)
    _ ≃ b * (sgn b * q') + r'     := AA.substL AA.assoc
    _ = b * q + r                 := rfl
  have : r ≥ 0 := from_natural_respects_le.mp ‹r' ≥ 0›
  have : abs r < abs b := calc
    _ = abs r  := rfl
    _ ≃ r      := abs_ident ‹r ≥ 0›
    _ = (r':ℤ) := rfl
    _ < (m:ℤ)  := from_natural_respects_lt.mp ‹r' < m›
    _ ≃ abs b  := ‹(m:ℤ) ≃ abs b›

  show EuclideanDivision a b from {
    quotient := q
    remainder := r
    div_eqv := ‹a ≃ b * q + r›
    rem_mag := ‹abs r < abs b›
    rem_sgn := ‹r ≥ 0›
  }

/-- Definition of integer Euclidean division. -/
def div_euclidean (a b : ℤ) [AP (b ≄ 0)] : EuclideanDivision a b :=
  match show Either (a ≥ 0) (-a ≥ 0) from either_nonneg with
  | .inl (_ : a ≥ 0) =>
    show EuclideanDivision a b from div_euclidean_nonneg ‹a ≥ 0› b
  | .inr (_ : -a ≥ 0) =>
    let d' : EuclideanDivision (-a) b := div_euclidean_nonneg ‹-a ≥ 0› b
    let q' := d'.quotient
    let r' := d'.remainder
    have : a ≃ b * -q' + -r' := calc
      _ = a               := rfl
      _ ≃ -(-a)           := Rel.symm neg_involutive
      _ ≃ -(b * q' + r')  := AA.subst₁ d'.div_eqv
      _ ≃ -(b * q') + -r' := neg_compat_add
      _ ≃ b * -q' + -r'   := AA.substL AA.scompatR
    have : r' ≥ 0 := d'.rem_sgn

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
      have : r' ≤ abs b := calc
        _ = r'     := rfl
        _ ≃ abs r' := Rel.symm (abs_ident ‹r' ≥ 0›)
        _ ≤ abs b  := le_split.mpr (Or.inl d'.rem_mag)
      have : r ≥ 0 := calc
        _ = r             := rfl
        _ = abs b - r'    := rfl
        _ ≥ abs b - abs b := le_substR_sub ‹r' ≤ abs b›
        _ ≃ 0             := sub_same
      have : abs r < abs b := calc
        _ = abs r      := rfl
        _ ≃ r          := abs_ident ‹r ≥ 0›
        _ = abs b - r' := rfl
        _ < abs b - 0  := lt_substR_sub ‹r' > 0›
        _ ≃ abs b      := sub_identR

      show EuclideanDivision a b from {
        quotient := q
        remainder := r
        div_eqv := ‹a ≃ b * q + r›
        rem_mag := ‹abs r < abs b›
        rem_sgn := ‹r ≥ 0›
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
      have : abs r < abs b := calc
        _ = abs r := rfl
        _ ≃ r     := abs_ident ‹r ≥ 0›
        _ < abs b := lt_from_le_neqv ‹r ≤ abs b› ‹r ≄ abs b›

      show EuclideanDivision a b from {
        quotient := q
        remainder := r
        div_eqv := ‹a ≃ b * q + r›
        rem_mag := ‹abs r < abs b›
        rem_sgn := ‹r ≥ 0›
      }

variable [Natural.Exponentiation ℕ ℤ]

/-- Definition of integer floored division. -/
def div_floored (a b : ℤ) [AP (b ≄ 0)] : FlooredDivision a b :=
  /- Find the natural number equivalent to the dividend's absolute value -/
  have : abs a ≥ 0 := abs_nonneg
  let an : { n : ℕ // abs a ≃ n } := nonneg_to_natural ‹abs a ≥ 0›
  let n := an.val
  have : (n:ℤ) ≃ abs a := Rel.symm an.property

  /- Find the natural number equivalent to the divisor's absolute value -/
  have : 0 ≤ abs b := abs_nonneg
  have : 0 ≄ abs b := Rel.symm (mt abs_zero.mpr ‹AP (b ≄ 0)›.ev)
  have : abs b > 0 := lt_from_le_neqv ‹0 ≤ abs b› ‹0 ≄ abs b›
  let bn : { m : ℕ // abs b ≃ m ∧ m > 0 } := pos_to_natural ‹abs b > 0›
  let m := bn.val
  have : (m:ℤ) ≃ abs b := Rel.symm bn.property.left
  have : m > 0 := bn.property.right
  have : AP (m ≄ 0) := AP.mk (Natural.neqv_zero_from_gt_zero ‹m > 0›)

  /- Natural number division and results -/
  let d' := Natural.divide n m
  let q' := d'.quotient
  let r' := d'.remainder
  have : n ≃ m * q' + r' := d'.div_eqv
  have : r' ≥ 0 := Natural.ge_zero
  have : (r':ℤ) ≥ 0 := from_natural_respects_le.mp ‹r' ≥ 0›
  have : r' < m := d'.rem_ub

  have : abs a ≃ abs b * q' + r' := calc
    _ = abs a                     := rfl
    _ ≃ (n:ℤ)                     := Rel.symm ‹(n:ℤ) ≃ abs a›
    _ ≃ ((m * q' + r' : ℕ):ℤ)     := AA.subst₁ d'.div_eqv
    _ ≃ ((m * q' : ℕ):ℤ) + (r':ℤ) := AA.compat₂
    _ ≃ (m:ℤ) * (q':ℤ) + (r':ℤ)   := AA.substL AA.compat₂
    _ ≃ abs b * q' + r'           := AA.substL (AA.substL ‹(m:ℤ) ≃ abs b›)
  have expand_a : a ≃ (abs b * q') * sgn a + r' * sgn a := calc
    _ = a                                 := rfl
    _ ≃ abs a * sgn a                     := Rel.symm abs_mul_sgn
    _ ≃ (abs b * q' + r') * sgn a         := AA.substL ‹abs a ≃ abs b * q' + r'›
    _ ≃ (abs b * q') * sgn a + r' * sgn a := AA.distribR

  /-
  The solutions for `a * b` nonnegative vs. negative are different enough that
  handling them separately keeps the definitions of `q` and `r` simpler, and
  reduces the complexity of the proofs.
  -/
  match show Either (a * b ≥ 0) (a * b < 0) from either_ge_lt with
  | .inl (_ : a * b ≥ 0) =>
    let q : ℤ := q'
    let r : ℤ := r' * sgn a

    /- Prove div_eqv -/
    have : (sgn a * sgn b) * q' ≃ q' :=
      match show a * b > 0 ∨ a * b ≃ 0 from ge_split.mp ‹a * b ≥ 0› with
      | .inl (_ : a * b > 0) =>
        calc
          _ = (sgn a * sgn b) * q' := rfl
          _ ≃ sgn (a * b) * q'     := AA.substL (Rel.symm sgn_compat_mul)
          _ ≃ 1 * q'               := AA.substL (gt_zero_sgn.mp ‹a * b > 0›)
          _ ≃ q'                   := AA.identL
      | .inr (_ : a * b ≃ 0) =>
        have : a ≃ 0 ∨ b ≃ 0 := mul_split_zero.mp ‹a * b ≃ 0›
        have : a ≃ 0 := match ‹a ≃ 0 ∨ b ≃ 0› with
        | .inl (_ : a ≃ 0) => ‹a ≃ 0›
        | .inr (_ : b ≃ 0) => absurd ‹b ≃ 0› ‹AP (b ≄ 0)›.ev
        have : (n:ℤ) ≃ 0 := calc
          _ = (n:ℤ) := rfl
          _ ≃ abs a := ‹(n:ℤ) ≃ abs a›
          _ ≃ 0     := abs_zero.mp ‹a ≃ 0›
        have : n ≃ 0 := AA.inject ‹(n:ℤ) ≃ (0:ℕ)›
        have (And.intro (_ : q' ≃ 0) _) := Natural.div_zero.mp ‹n ≃ 0›
        have : (q':ℤ) ≃ (0:ℕ) := AA.subst₁ ‹q' ≃ 0›
        calc
          _ = (sgn a * sgn b) * q' := rfl
          _ ≃ (sgn a * sgn b) * 0  := AA.substR ‹(q':ℤ) ≃ 0›
          _ ≃ 0                    := AA.absorbR
          _ ≃ q'                   := Rel.symm ‹(q':ℤ) ≃ 0›
    have expand_q : q ≃ sgn b * q' * sgn a := Rel.symm $ calc
      _ = sgn b * q' * sgn a   := rfl
      _ ≃ sgn a * (sgn b * q') := AA.comm
      _ ≃ (sgn a * sgn b) * q' := Rel.symm AA.assoc
      _ ≃ q'                   := ‹(sgn a * sgn b) * q' ≃ q'›
    have expand_bq : b * q ≃ (abs b * q') * sgn a := Rel.symm $ calc
      _ = (abs b * q') * sgn a       := rfl
      _ ≃ (b * sgn b * q') * sgn a   := AA.substL (AA.substL abs_sgn)
      _ ≃ (b * (sgn b * q')) * sgn a := AA.substL AA.assoc
      _ ≃ b * (sgn b * q' * sgn a)   := AA.assoc
      _ ≃ b * q                      := AA.substR (Rel.symm expand_q)
    have : a ≃ b * q + r := Rel.symm $ calc
      _ = b * q + r                         := rfl
      _ ≃ (abs b * q') * sgn a + r          := AA.substL expand_bq
      _ = (abs b * q') * sgn a + r' * sgn a := rfl
      _ ≃ a                                 := Rel.symm expand_a

    /- Prove rem_mag -/
    have : abs r < abs b := calc
      _ = abs r                    := rfl
      _ = abs (r' * sgn a)         := rfl
      _ ≃ abs (r':ℤ) * abs (sgn a) := abs_compat_mul
      _ ≃ r' * abs (sgn a)         := AA.substL (abs_ident ‹(r':ℤ) ≥ 0›)
      _ ≃ r' * (sgn a)^2           := AA.substR abs_sgn_sqr
      _ ≤ r' * 1                   := le_mulL_nonneg ‹(r':ℤ) ≥ 0› sgn_sqr_ub
      _ ≃ r'                       := AA.identR
      _ < m                        := from_natural_respects_lt.mp ‹r' < m›
      _ ≃ abs b                    := ‹(m:ℤ) ≃ abs b›

    /- Prove rem_sgn -/
    have : sgn a * sgn b ≥ 0 := calc
      _ = sgn a * sgn b := rfl
      _ ≃ sgn (a * b)   := Rel.symm sgn_compat_mul
      _ ≥ 0             := sgn_preserves_ge_zero.mp ‹a * b ≥ 0›
    have : abs b * r' ≥ 0 := mul_preserves_nonneg abs_nonneg ‹(r':ℤ) ≥ 0›
    have : (sgn a * sgn b) * (abs b * r') ≥ 0 :=
      mul_preserves_nonneg ‹sgn a * sgn b ≥ 0› ‹abs b * r' ≥ 0›
    have : r * b ≥ 0 := calc
      _ = r * b                          := rfl
      _ = (r' * sgn a) * b               := rfl
      _ ≃ (r' * sgn a) * (abs b * sgn b) := AA.substR (Rel.symm abs_mul_sgn)
      _ ≃ (sgn a * r') * (abs b * sgn b) := AA.substL AA.comm
      _ ≃ (sgn a * sgn b) * (abs b * r') := AA.expr_xxfxxff_lr_swap_rr
      _ ≥ 0                              := ‹(sgn a * sgn b) * (abs b * r') ≥ 0›

    show FlooredDivision a b from {
      quotient := q
      remainder := r
      div_eqv := ‹a ≃ b * q + r›
      rem_mag := ‹abs r < abs b›
      rem_sgn := ‹r * b ≥ 0›
    }

  | .inr (_ : a * b < 0) =>
    have : sgn a * sgn b ≃ -1 := calc
      _ = sgn a * sgn b := rfl
      _ ≃ sgn (a * b)   := Rel.symm sgn_compat_mul
      _ ≃ -1            := lt_zero_sgn.mp ‹a * b < 0›

    let sr' := sgn (r':ℤ)
    let q := -(q' + sr')
    let r := b * sr' + r' * sgn a

    /- Prove div_eqv -/
    have expand_bq : -(b * q') ≃ (abs b * q') * sgn a := Rel.symm $ calc
      _ = (abs b * q') * sgn a       := rfl
      _ ≃ (b * sgn b * q') * sgn a   := AA.substL (AA.substL abs_sgn)
      _ ≃ (sgn b * b * q') * sgn a   := AA.substL (AA.substL AA.comm)
      _ ≃ sgn b * (b * q') * sgn a   := AA.substL AA.assoc
      _ ≃ sgn a * (sgn b * (b * q')) := AA.comm
      _ ≃ sgn a * sgn b * (b * q')   := Rel.symm AA.assoc
      _ ≃ -1 * (b * q')              := AA.substL ‹sgn a * sgn b ≃ -1›
      _ ≃ -(b * q')                  := mul_neg_one
    have reduce : b * -(q' + sr') + b * sr' ≃ -(b * q') := calc
      _ = b * -(q' + sr') + b * sr'      := rfl
      _ ≃ b * (-q' + -sr') + b * sr'     := AA.substL (AA.substR neg_compat_add)
      _ ≃ b * -q' + b * -sr' + b * sr'   := AA.substL AA.distribL
      _ ≃ b * -q' + (b * -sr' + b * sr') := AA.assoc
      _ ≃ b * -q' + b * (-sr' + sr')     := AA.substR (Rel.symm AA.distribL)
      _ ≃ b * -q' + b * 0                := AA.substR (AA.substR AA.inverseL)
      _ ≃ b * -q' + 0                    := AA.substR AA.absorbR
      _ ≃ b * -q'                        := AA.identR
      _ ≃ -(b * q')                      := Rel.symm AA.scompatR
    have : a ≃ b * q + r := Rel.symm $ calc
      _ = b * q + r                                := rfl
      _ = b * -(q' + sr') + (b * sr' + r' * sgn a) := rfl
      _ ≃ b * -(q' + sr') + b * sr' + r' * sgn a   := Rel.symm AA.assoc
      _ ≃ -(b * q') + r' * sgn a                   := AA.substL reduce
      _ ≃ (abs b * q') * sgn a + r' * sgn a        := AA.substL expand_bq
      _ ≃ a                                        := Rel.symm expand_a

    /- Prove rem_mag -/
    have abs_sgn' {x : ℤ} : x ≃ abs x * sgn x := Rel.symm abs_mul_sgn
    have expand_r : r ≃ (abs b * sr') * sgn b + r' * sgn a := calc
      _ = r                                  := rfl
      _ = b * sr' + r' * sgn a               := rfl
      _ ≃ abs b * sgn b * sr' + r' * sgn a   := AA.substL (AA.substL abs_sgn')
      _ ≃ sgn b * abs b * sr' + r' * sgn a   := AA.substL (AA.substL AA.comm)
      _ ≃ sgn b * (abs b * sr') + r' * sgn a := AA.substL AA.assoc
      _ ≃ abs b * sr' * sgn b + r' * sgn a   := AA.substL AA.comm
    have : b * a < 0 := trans AA.comm ‹a * b < 0›
    have : abs r ≃ abs (abs b * sr' - r') := calc
      _ = abs r                                  := rfl
      _ ≃ abs (abs b * sr' * sgn b + r' * sgn a) := abs_subst expand_r
      _ ≃ abs (abs b * sr' - r')                 := abs_pos_neg_sum ‹b * a < 0›
    have factor : abs b * sr' - r' ≃ (abs b - r') * sr' := Rel.symm $ calc
      _ = (abs b - r') * sr'       := rfl
      _ ≃ abs b * sr' - r' * sr'   := AA.distribR
      _ ≃ abs b * sr' - abs (r':ℤ) := sub_substR (Rel.symm abs_sgn)
      _ ≃ abs b * sr' - r'         := sub_substR (abs_ident ‹(r':ℤ) ≥ 0›)
    have : r' ≤ m := Natural.le_split.mpr (Or.inl ‹r' < m›)
    have : abs b - r' ≥ 0 := calc
      _ = abs b - r'    := rfl
      _ ≥ abs b - m     := le_substR_sub (from_natural_respects_le.mp ‹r' ≤ m›)
      _ ≃ abs b - abs b := sub_substR ‹(m:ℤ) ≃ abs b›
      _ ≃ 0             := sub_same
    have : abs sr' ≃ sr' := calc
      _ = abs sr'                       := rfl
      _ = abs (sgn (r':ℤ))              := rfl
      _ ≃ sgn (r':ℤ) * sgn (sgn (r':ℤ)) := abs_sgn
      _ ≃ sgn (r':ℤ) * sgn (r':ℤ)       := AA.substR sgn_idemp
      _ ≃ (sgn (r':ℤ))^2                := Rel.symm Natural.pow_two
      _ ≃ sgn (r':ℤ)                    := sgn_sqr_nonneg.mpr ‹(r':ℤ) ≥ 0›
      _ = sr'                           := rfl
    have : (abs b - r') * sr' < abs b :=
      match show (r':ℤ) > 0 ∨ (r':ℤ) ≃ 0 from ge_split.mp ‹(r':ℤ) ≥ 0› with
      | .inl (_ : (r':ℤ) > 0) =>
        calc
          _ = (abs b - r') * sr' := rfl
          _ ≃ (abs b - r') * 1   := AA.substR (gt_zero_sgn.mp ‹(r':ℤ) > 0›)
          _ ≃ abs b - r'         := AA.identR
          _ < abs b - 0          := lt_substR_sub ‹0 < (r':ℤ)›
          _ ≃ abs b              := sub_identR
      | .inr (_ : (r':ℤ) ≃ 0) =>
        have : abs b ≄ 0 := mt abs_zero.mpr ‹AP (b ≄ 0)›.ev
        have : 0 ≤ abs b ∧ 0 ≄ abs b := And.intro abs_nonneg ‹0 ≄ abs b›
        calc
          _ = (abs b - r') * sr' := rfl
          _ ≃ (abs b - r') * 0   := AA.substR (sgn_zero.mp ‹(r':ℤ) ≃ 0›)
          _ ≃ 0                  := AA.absorbR
          _ < abs b              := lt_iff_le_neqv.mpr ‹0 ≤ abs b ∧ 0 ≄ abs b›
    have : abs r < abs b := calc
      _ = abs r                      := rfl
      _ ≃ abs (abs b * sr' - r')     := ‹abs r ≃ abs (abs b * sr' - r')›
      _ ≃ abs ((abs b - r') * sr')   := abs_subst factor
      _ ≃ abs (abs b - r') * abs sr' := abs_compat_mul
      _ ≃ (abs b - r') * abs sr'     := AA.substL (abs_ident ‹abs b - r' ≥ 0›)
      _ ≃ (abs b - r') * sr'         := AA.substR ‹abs sr' ≃ sr'›
      _ < abs b                      := ‹(abs b - r') * sr' < abs b›

    /- Prove rem_sgn -/
    let absr' := abs b * sr'
    have reduceL : b * sr' * b ≃ absr' * abs b := calc
      _ = b * sr' * b           := rfl
      _ ≃ b * (b * sr')         := AA.comm
      _ ≃ b * b * sr'           := Rel.symm AA.assoc
      _ ≃ b^2 * sr'             := AA.substL (Rel.symm Natural.pow_two)
      _ ≃ (abs b)^2 * sr'       := AA.substL (Rel.symm abs_sqr)
      _ ≃ abs b * abs b * sr'   := AA.substL Natural.pow_two
      _ ≃ abs b * (abs b * sr') := AA.assoc
      _ ≃ abs b * sr' * abs b   := AA.comm
      _ = absr' * abs b         := rfl
    have : sgn a * b ≃ -abs b := calc
      _ = sgn a * b               := rfl
      _ ≃ sgn a * (abs b * sgn b) := AA.substR abs_sgn'
      _ ≃ sgn a * (sgn b * abs b) := AA.substR AA.comm
      _ ≃ sgn a * sgn b * abs b   := Rel.symm AA.assoc
      _ ≃ -1 * abs b              := AA.substL ‹sgn a * sgn b ≃ -1›
      _ ≃ -abs b                  := mul_neg_one
    have reduceR : r' * sgn a * b ≃ -(absr' * r') := calc
      _ = r' * sgn a * b        := rfl
      _ ≃ r' * (sgn a * b)      := AA.assoc
      _ ≃ r' * -abs b           := AA.substR ‹sgn a * b ≃ -abs b›
      _ ≃ -abs b * r'           := AA.comm
      _ ≃ -abs b * abs (r':ℤ)   := AA.substR (Rel.symm (abs_ident ‹(r':ℤ) ≥ 0›))
      _ ≃ -abs b * (r' * sr')   := AA.substR abs_sgn
      _ ≃ -abs b * (sr' * r')   := AA.substR AA.comm
      _ ≃ -(abs b * (sr' * r')) := Rel.symm AA.scompatL
      _ ≃ -(abs b * sr' * r')   := AA.subst₁ (Rel.symm AA.assoc)
      _ = -(absr' * r')         := rfl
    have : sr' ≥ 0 := sgn_preserves_ge_zero.mp ‹(r':ℤ) ≥ 0›
    have : absr' ≥ 0 := mul_preserves_nonneg abs_nonneg ‹sr' ≥ 0›
    have : absr' * (abs b - r') ≥ 0 :=
      mul_preserves_nonneg ‹absr' ≥ 0› ‹abs b - r' ≥ 0›
    have : r * b ≥ 0 := calc
      _ = r * b                          := rfl
      _ = (b * sr' + r' * sgn a) * b     := rfl
      _ ≃ b * sr' * b + r' * sgn a * b   := AA.distribR
      _ ≃ absr' * abs b + r' * sgn a * b := AA.substL reduceL
      _ ≃ absr' * abs b + -(absr' * r')  := AA.substR reduceR
      _ ≃ absr' * abs b - absr' * r'     := Rel.symm sub_defn
      _ ≃ absr' * (abs b - r')           := Rel.symm AA.distribL
      _ ≥ 0                              := ‹absr' * (abs b - r') ≥ 0›

    show FlooredDivision a b from {
      quotient := q
      remainder := r
      div_eqv := ‹a ≃ b * q + r›
      rem_mag := ‹abs r < abs b›
      rem_sgn := ‹r * b ≥ 0›
    }

def division : Division ℤ := {
  div_euclidean := div_euclidean
  div_floored := div_floored
}

end Lean4Axiomatic.Integer.Impl.Generic
