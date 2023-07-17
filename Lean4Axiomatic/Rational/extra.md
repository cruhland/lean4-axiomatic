# Rationals: extra results

The following code block contains theorems that aren't needed right now, but
took some effort to prove. Keeping them here in case they are useful later.

```lean4
import Lean4Axiomatic.Rational.Metric

namespace Lean4Axiomatic.Rational

open Lean4Axiomatic.Metric (abs dist)
open Lean4Axiomatic.Signed (sgn)

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ] [Subtraction ℚ]
  [Multiplication ℚ] [Reciprocation ℚ] [Division ℚ]
  [Sign ℚ] [Order ℚ] [Metric ℚ]

theorem neg_eqv_zero {p : ℚ} : p ≃ -p ↔ p ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≃ -p)
    show p ≃ 0
    have : sgn p ≃ 0 := calc
      _ ≃ sgn p        := Rel.refl
      _ ≃ sgn (p + p)  := Rel.symm (add_preserves_sign Rel.refl Rel.refl)
      _ ≃ sgn (-p + p) := sgn_subst (add_substL ‹p ≃ -p›)
      _ ≃ sgn (0:ℚ)    := sgn_subst add_inverseL
      _ ≃ 0            := sgn_zero.mp eqv_refl
    have : p ≃ 0 := sgn_zero.mpr ‹sgn p ≃ 0›
    exact this
  case mpr =>
    intro (_ : p ≃ 0)
    show p ≃ -p
    calc
      _ ≃ p  := eqv_refl
      _ ≃ 0  := ‹p ≃ 0›
      _ ≃ -p := eqv_symm (neg_preserves_zero.mpr ‹p ≃ 0›)

theorem abs_ident_from_zero {p : ℚ} : p ≃ 0 → abs p ≃ p := by
  intro (_ : p ≃ 0)
  show abs p ≃ p
  calc
    _ ≃ abs p := eqv_refl
    _ ≃ 0     := abs_zero.mpr ‹p ≃ 0›
    _ ≃ p     := eqv_symm ‹p ≃ 0›

theorem abs_nonnegative {p : ℚ} : sgn p ≄ -1 ↔ abs p ≃ p := by
  apply Iff.intro
  case mp =>
    intro (_ : sgn p ≄ -1)
    show abs p ≃ p
    let OneOfThree := AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1)
    have : OneOfThree := sgn_trichotomy p
    match this with
    | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
      have : p ≃ 0 := sgn_zero.mpr ‹sgn p ≃ 0›
      have : abs p ≃ p := abs_ident_from_zero ‹p ≃ 0›
      exact this
    | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
      have : abs p ≃ p := abs_positive ‹sgn p ≃ 1›
      exact this
    | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
      have : abs p ≃ p := absurd ‹sgn p ≃ -1› ‹sgn p ≄ -1›
      exact this
  case mpr =>
    intro (_ : abs p ≃ p) (_ : sgn p ≃ -1)
    show False
    have : p ≃ -p := calc
      _ ≃ p              := eqv_refl
      _ ≃ abs p          := eqv_symm ‹abs p ≃ p›
      _ ≃ p * sgn p      := abs_sgn
      _ ≃ p * ((-1:ℤ):ℚ) := mul_substR (from_integer_subst ‹sgn p ≃ -1›)
      _ ≃ p * (-1)       := mul_substR neg_compat_from_integer
      _ ≃ (-1) * p       := mul_comm
      _ ≃ -p             := mul_neg_one
    have : p ≃ 0 := neg_eqv_zero.mp ‹p ≃ -p›
    have : sgn p ≃ 0 := sgn_zero.mp ‹p ≃ 0›
    let TwoOfThree := AA.TwoOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1)
    have : TwoOfThree := AA.TwoOfThree.oneAndThree ‹sgn p ≃ 0› ‹sgn p ≃ -1›
    have : ¬TwoOfThree := Integer.signs_distinct
    have : False := absurd ‹TwoOfThree› ‹¬TwoOfThree›
    exact this

theorem abs_nonpositive {p : ℚ} : sgn p ≄ 1 ↔ abs p ≃ -p := by
  apply Iff.intro
  case mp =>
    intro (_ : sgn p ≄ 1)
    show abs p ≃ -p
    let OneOfThree := AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1)
    have : OneOfThree := sgn_trichotomy p
    match this with
    | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
      have : p ≃ 0 := sgn_zero.mpr ‹sgn p ≃ 0›
      have : abs p ≃ -p := calc
        _ ≃ abs p := eqv_refl
        _ ≃ p := abs_ident_from_zero ‹p ≃ 0›
        _ ≃ -p := neg_eqv_zero.mpr ‹p ≃ 0›
      exact this
    | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
      have : abs p ≃ -p := absurd ‹sgn p ≃ 1› ‹sgn p ≄ 1›
      exact this
    | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
      have : abs p ≃ -p := abs_negative ‹sgn p ≃ -1›
      exact this
  case mpr =>
    intro (_ : abs p ≃ -p) (_ : sgn p ≃ 1)
    show False
    have : p ≃ -p := calc
      _ ≃ p         := eqv_refl
      _ ≃ p * 1     := eqv_symm mul_identR
      _ ≃ p * sgn p := mul_substR (from_integer_subst (Rel.symm ‹sgn p ≃ 1›))
      _ ≃ abs p     := eqv_symm abs_sgn
      _ ≃ -p        := ‹abs p ≃ -p›
    have : p ≃ 0 := neg_eqv_zero.mp ‹p ≃ -p›
    have : sgn p ≃ 0 := sgn_zero.mp ‹p ≃ 0›
    let TwoOfThree := AA.TwoOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1)
    have : TwoOfThree := AA.TwoOfThree.oneAndTwo ‹sgn p ≃ 0› ‹sgn p ≃ 1›
    have : ¬TwoOfThree := Integer.signs_distinct
    have : False := absurd ‹TwoOfThree› ‹¬TwoOfThree›
    exact this

theorem dist_sum_comm
    {p q r : ℚ} : dist p r ≃ dist p q + dist q r
    → dist r p ≃ dist r q + dist q p
    := by
  intro (_ : dist p r ≃ dist p q + dist q r)
  show dist r p ≃ dist r q + dist q p
  calc
    _ ≃ dist r p            := eqv_refl
    _ ≃ dist p r            := dist_comm
    _ ≃ dist p q + dist q r := ‹dist p r ≃ dist p q + dist q r›
    _ ≃ dist q p + dist q r := add_substL dist_comm
    _ ≃ dist q p + dist r q := add_substR dist_comm
    _ ≃ dist r q + dist q p := add_comm

theorem dist_diff_le {p q : ℚ} : dist p q ≃ q - p ↔ p ≤ q := by
  apply Iff.intro
  case mp =>
    intro (_ : dist p q ≃ q - p)
    show p ≤ q
    have : abs (p - q) ≃ -(p - q) := calc
      _ ≃ abs (p - q) := eqv_refl
      _ ≃ dist p q    := eqv_symm dist_abs
      _ ≃ q - p       := ‹dist p q ≃ q - p›
      _ ≃ -(p - q)    := eqv_symm neg_sub
    have : sgn (p - q) ≄ 1 := abs_nonpositive.mpr ‹abs (p - q) ≃ -(p - q)›
    have : p ≤ q := le_sgn.mpr this
    exact this
  case mpr =>
    intro (_ : p ≤ q)
    show dist p q ≃ q - p
    have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
    calc
      _ ≃ dist p q    := eqv_refl
      _ ≃ abs (p - q) := dist_abs
      _ ≃ -(p - q)    := abs_nonpositive.mp ‹sgn (p - q) ≄ 1›
      _ ≃ q - p       := neg_sub

theorem dist_sum_from_order
    {p q r : ℚ} : p ≤ q ∧ q ≤ r → dist p r ≃ dist p q + dist q r
    := by
  intro (And.intro (_ : p ≤ q) (_ : q ≤ r))
  show dist p r ≃ dist p q + dist q r
  have : p ≤ r := le_trans ‹p ≤ q› ‹q ≤ r›
  have : dist p r ≃ r - p := dist_diff_le.mpr ‹p ≤ r›
  have : dist p q ≃ q - p := dist_diff_le.mpr ‹p ≤ q›
  have : dist q r ≃ r - q := dist_diff_le.mpr ‹q ≤ r›
  calc
    _ ≃ dist p r            := eqv_refl
    _ ≃ r - p               := ‹dist p r ≃ r - p›
    _ ≃ (r - q) + (q - p)   := eqv_symm add_sub_telescope
    _ ≃ dist q r + (q - p)  := add_substL (eqv_symm ‹dist q r ≃ r - q›)
    _ ≃ dist q r + dist p q := add_substR (eqv_symm ‹dist p q ≃ q - p›)
    _ ≃ dist p q + dist q r := add_comm

-- TODO: Introduce syntax for ≯
theorem le_from_not_gt {p q : ℚ} : ¬(p > q) → p ≤ q := by
  intro (_ : ¬(p > q))
  show p ≤ q
  let OneOfThree := AA.OneOfThree (p < q) (p ≃ q) (p > q)
  have : OneOfThree := (order_trichotomy p q).atLeastOne
  match this with
  | AA.OneOfThree.first (_ : p < q) =>
    have : p ≤ q := le_cases.mpr (Or.inl ‹p < q›)
    exact this
  | AA.OneOfThree.second (_ : p ≃ q) =>
    have : p ≤ q := le_cases.mpr (Or.inr ‹p ≃ q›)
    exact this
  | AA.OneOfThree.third (_ : p > q) =>
    have : p ≤ q := absurd ‹p > q› ‹¬(p > q)›
    exact this

theorem order_from_dist_sum
    {p q r : ℚ} : dist p r ≃ dist p q + dist q r → p ≤ r → p ≤ q ∧ q ≤ r
    := by
  intro (_ : dist p r ≃ dist p q + dist q r) (_ : p ≤ r)
  show p ≤ q ∧ q ≤ r
  have : dist p r ≃ r - p := dist_diff_le.mpr ‹p ≤ r›

  have : ¬(p > q) := by
    intro (_ : q < p)
    show False
    have : q ≤ p := le_cases.mpr (Or.inl ‹q < p›)
    have : dist p q ≃ p - q := eqv_trans dist_comm (dist_diff_le.mpr ‹q ≤ p›)
    have : dist q r ≃ r - q := dist_diff_le.mpr (le_trans ‹q ≤ p› ‹p ≤ r›)

    have : (-q + -q) + (p + r) ≃ -p + r := calc
      _ ≃ (-q + -q) + (p + r) := eqv_refl
      _ ≃ (p + r) + (-q + -q) := add_comm
      _ ≃ (p + -q) + (r + -q) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ (p - q) + (r + -q)  := add_substL (eqv_symm sub_add_neg)
      _ ≃ (p - q) + (r - q)   := add_substR (eqv_symm sub_add_neg)
      _ ≃ dist p q + (r - q)  := add_substL (eqv_symm ‹dist p q ≃ p - q›)
      _ ≃ dist p q + dist q r := add_substR (eqv_symm ‹dist q r ≃ r - q›)
      _ ≃ dist p r            := eqv_symm ‹dist p r ≃ dist p q + dist q r›
      _ ≃ r - p               := ‹dist p r ≃ r - p›
      _ ≃ r + -p              := sub_add_neg
      _ ≃ -p + r              := add_comm
    have : -q + -q ≃ -p + -p := calc
      _ ≃ -q + -q                      := eqv_refl
      _ ≃ (-q + -q) + 0                := eqv_symm add_identR
      _ ≃ (-q + -q) + ((p+r) + -(p+r)) := add_substR (eqv_symm add_inverseR)
      _ ≃ ((-q + -q) + (p+r)) + -(p+r) := eqv_symm add_assoc
      _ ≃ (-p + r) + -(p + r)          := add_substL ‹(-q + -q) + (p+r) ≃ -p+r›
      _ ≃ (-p + r) + (-p + -r)         := add_substR neg_compat_add
      _ ≃ (-p + -p) + (r + -r)         := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ (-p + -p) + 0                := add_substR add_inverseR
      _ ≃ -p + -p                      := add_identR
    have double_negate {x : ℚ} : x ≃ (-x + -x) * (-2)⁻¹ := calc
      _ ≃ x                   := eqv_refl
      _ ≃ x * 1               := eqv_symm mul_identR
      _ ≃ x * ((-2) * (-2)⁻¹) := mul_substR (eqv_symm mul_inverseR)
      _ ≃ (x * -2) * (-2)⁻¹   := eqv_symm mul_assoc
      _ ≃ -(x * 2) * (-2)⁻¹   := mul_substL (eqv_symm neg_scompatR_mul)
      _ ≃ -(2 * x) * (-2)⁻¹   := mul_substL (neg_subst mul_comm)
      _ ≃ -(x + x) * (-2)⁻¹   := mul_substL (neg_subst mul_two_add)
      _ ≃ (-x + -x) * (-2)⁻¹  := mul_substL neg_compat_add
    have : q ≃ p := calc
      _ ≃ q                  := eqv_refl
      _ ≃ (-q + -q) * (-2)⁻¹ := double_negate
      _ ≃ (-p + -p) * (-2)⁻¹ := mul_substL ‹-q + -q ≃ -p + -p›
      _ ≃ p                  := eqv_symm double_negate

    let TwoOfThree := AA.TwoOfThree (q < p) (q ≃ p) (q > p)
    have : TwoOfThree := AA.TwoOfThree.oneAndTwo ‹q < p› ‹q ≃ p›
    have : ¬TwoOfThree := (order_trichotomy q p).atMostOne
    exact absurd ‹TwoOfThree› ‹¬TwoOfThree›

  have : ¬(q > r) := by
    intro (_ : r < q)
    show False
    have : r ≤ q := le_cases.mpr (Or.inl ‹r < q›)
    have : dist p q ≃ q - p := dist_diff_le.mpr (le_trans ‹p ≤ r› ‹r ≤ q›)
    have : dist q r ≃ q - r := eqv_trans dist_comm (dist_diff_le.mpr ‹r ≤ q›)

    have : r + -p ≃ (q + q) + -(r + p) := calc
      _ ≃ r + -p              := eqv_refl
      _ ≃ r - p               := eqv_symm sub_add_neg
      _ ≃ dist p r            := eqv_symm ‹dist p r ≃ r - p›
      _ ≃ dist p q + dist q r := ‹dist p r ≃ dist p q + dist q r›
      _ ≃ (q - p) + dist q r  := add_substL ‹dist p q ≃ q - p›
      _ ≃ (q - p) + (q - r)   := add_substR ‹dist q r ≃ q - r›
      _ ≃ (q + -p) + (q - r)  := add_substL sub_add_neg
      _ ≃ (q + -p) + (q + -r) := add_substR sub_add_neg
      _ ≃ (q + q) + (-p + -r) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ (q + q) + (-r + -p) := add_substR add_comm
      _ ≃ (q + q) + -(r + p)  := add_substR (eqv_symm neg_compat_add)
    have : r + r ≃ q + q := calc
      _ ≃ r + r                          := eqv_refl
      _ ≃ (r + r) + 0                    := eqv_symm add_identR
      _ ≃ (r + r) + (-p + p)             := add_substR (eqv_symm add_inverseL)
      _ ≃ (r + -p) + (r + p)             := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ ((q + q) + -(r + p)) + (r + p) := add_substL this
      _ ≃ (q + q) + (-(r + p) + (r + p)) := add_assoc
      _ ≃ (q + q) + 0                    := add_substR add_inverseL
      _ ≃ q + q                          := add_identR
    have double {x : ℚ} : x ≃ (x + x) * 2⁻¹ := calc
      _ ≃ x             := eqv_refl
      _ ≃ x * 1         := eqv_symm mul_identR
      _ ≃ x * (2 * 2⁻¹) := mul_substR (eqv_symm mul_inverseR)
      _ ≃ (x * 2) * 2⁻¹ := eqv_symm mul_assoc
      _ ≃ (2 * x) * 2⁻¹ := mul_substL mul_comm
      _ ≃ (x + x) * 2⁻¹ := mul_substL mul_two_add
    have : r ≃ q := calc
      _ ≃ r             := eqv_refl
      _ ≃ (r + r) * 2⁻¹ := double
      _ ≃ (q + q) * 2⁻¹ := mul_substL ‹r + r ≃ q + q›
      _ ≃ q             := eqv_symm double

    let TwoOfThree := AA.TwoOfThree (r < q) (r ≃ q) (r > q)
    have : TwoOfThree := AA.TwoOfThree.oneAndTwo ‹r < q› ‹r ≃ q›
    have : ¬TwoOfThree := (order_trichotomy r q).atMostOne
    exact absurd ‹TwoOfThree› ‹¬TwoOfThree›

  have : p ≤ q := le_from_not_gt ‹¬(p > q)›
  have : q ≤ r := le_from_not_gt ‹¬(q > r)›
  exact And.intro ‹p ≤ q› ‹q ≤ r›

theorem between_dist
    {p q r : ℚ} : p⊣ q ⊢r ↔ dist p r ≃ dist p q + dist q r
    := by
  apply Iff.intro
  case mp =>
    intro (_ : p⊣ q ⊢r)
    show dist p r ≃ dist p q + dist q r
    have : p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p := between_order.mp ‹p⊣ q ⊢r›
    match this with
    | Or.inl (_ : p ≤ q ∧ q ≤ r) =>
      have := ‹p ≤ q ∧ q ≤ r›
      have : dist p r ≃ dist p q + dist q r := dist_sum_from_order this
      exact this
    | Or.inr (_ : r ≤ q ∧ q ≤ p) =>
      have := ‹r ≤ q ∧ q ≤ p›
      have : dist r p ≃ dist r q + dist q p := dist_sum_from_order this
      have : dist p r ≃ dist p q + dist q r := dist_sum_comm this
      exact this
  case mpr =>
    intro (dist_sum : dist p r ≃ dist p q + dist q r)
    show p⊣ q ⊢r
    have : p ≤ r ∨ r ≤ p := le_dichotomy
    have : p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p :=
      match this with
      | Or.inl (_ : p ≤ r) =>
        have : p ≤ q ∧ q ≤ r := order_from_dist_sum dist_sum ‹p ≤ r›
        Or.inl this
      | Or.inr (_ : r ≤ p) =>
        have : dist r p ≃ dist r q + dist q p := dist_sum_comm dist_sum
        have : r ≤ q ∧ q ≤ p := order_from_dist_sum this ‹r ≤ p›
        Or.inr this
    have : p⊣ q ⊢r := between_order.mpr ‹p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p›
    exact this

end Lean4Axiomatic.Rational
```
