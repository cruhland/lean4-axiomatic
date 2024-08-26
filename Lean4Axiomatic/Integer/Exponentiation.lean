import Lean4Axiomatic.Integer.Order

/-!
# Integers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Integer

open Logic (AP iff_subst_covar or_mapL or_mapR)
open Natural (step)
open Signed (Positive)

/-! ## Derived properties for exponentiation to a natural number -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]
  [Negation ℤ] [Subtraction ℤ] [Sign ℤ] [Order ℤ]
  [Natural.Exponentiation ℕ ℤ (· * ·)]

/--
The operations of `sgn` and `·^n` (i.e. raising to a natural number power) give
the same result when applied to an integer in either order.

**Property and proof intuition**: Take the property that `sgn` is compatible
with multiplication (`sgn (a * b) ≃ sgn a * sgn b`) and repeatedly apply it to
the product formed by `a^n`.
-/
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

/--
All integer squares are nonnegative.

**Property intuition**: A negative times a negative is positive.

**Proof intuition**: Direct corollary of `nonneg_square`.
-/
theorem sqr_nonneg {a : ℤ} : a^2 ≥ 0 := by
  have : sgn (a * a) ≄ -1 := nonneg_square
  calc
    _ = a^2   := rfl
    _ ≃ a * a := Natural.pow_two
    _ ≥ 0     := ge_zero_sgn.mpr ‹sgn (a * a) ≄ -1›

/--
Zero and one are the only integers that are identical to their squares.

**Property intuition**: Negative integers become positive when squared, and all
integers greater than one increase in magnitude.

**Proof intuition**: Corollary of `mul_identR_reasons`.
-/
theorem sqr_idemp_reasons {a : ℤ} : a^2 ≃ a ↔ a ≃ 0 ∨ a ≃ 1 := calc
  _ ↔ a^2 ≃ a       := Iff.rfl
  _ ↔ a * a ≃ a     := AA.eqv_substL_iff Natural.pow_two
  _ ↔ a ≃ 0 ∨ a ≃ 1 := mul_identR_reasons

/--
Squaring the sign of an integer leaves it the same iff the integer is
nonnegative.

**Property and proof intuition**: Only zero and one stay the same when squared,
and those are the two sign values of nonnegative integers.
-/
theorem sgn_sqr_nonneg {a : ℤ} : (sgn a)^2 ≃ sgn a ↔ a ≥ 0 := calc
  _ ↔ (sgn a)^2 ≃ sgn a     := Iff.rfl
  _ ↔ sgn a ≃ 0 ∨ sgn a ≃ 1 := sqr_idemp_reasons
  _ ↔ a ≃ 0 ∨ sgn a ≃ 1     := iff_subst_covar or_mapL sgn_zero.symm
  _ ↔ a ≃ 0 ∨ a > 0         := iff_subst_covar or_mapR gt_zero_sgn.symm
  _ ↔ a > 0 ∨ a ≃ 0         := Or.comm
  _ ↔ a ≥ 0                 := ge_split.symm

/--
Raising an integer to _any_ positive natural number power has no effect if
just squaring the integer has no effect.

**Property and proof intuition**: By induction, any power greater than two can
be reduced to the squaring case.
-/
theorem pow_absorbL {a : ℤ} {n : ℕ} : n ≥ 1 → a^2 ≃ a → a^n ≃ a := by
  intro (_ : n ≥ 1) (_ : a^2 ≃ a)
  show a^n ≃ a

  let motive := λ (x : ℕ) => a^x ≃ a
  have motive_subst {x₁ x₂ : ℕ} : x₁ ≃ x₂ → motive x₁ → motive x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : a^x₁ ≃ a)
    show a^x₂ ≃ a
    calc
      _ = a^x₂ := rfl
      _ ≃ a^x₁ := Natural.pow_substR (Rel.symm ‹x₁ ≃ x₂›)
      _ ≃ a    := ‹a^x₁ ≃ a›

  apply Natural.ind_from motive_subst ‹n ≥ 1›
  case base =>
    show a^1 ≃ a
    exact Natural.pow_one
  case next =>
    intro (k : ℕ) (_ : k ≥ 1) (ih : a^k ≃ a)
    show a^(step k) ≃ a
    calc
      _ = a^(step k) := rfl
      _ ≃ a^k * a    := Natural.pow_step
      _ ≃ a * a      := AA.substL ih
      _ ≃ a^2        := Rel.symm Natural.pow_two
      _ ≃ a          := ‹a^2 ≃ a›

/--
The difference of two integer squares can be rewritten as the product of two
factors linear in the original integers.

**Property intuition**: Using plane geometry where `a^2` and `b^2` are areas of
actual squares. Without loss of generality, let `a` be the side length of the
larger square and let `b` be the side length of the smaller. Then `a^2 - b^2`
is the area of the larger square that is not covered by the smaller square
(imagine the smaller square is fully inside the larger, sharing one corner).
The area of this region can be found by adding the areas of the rectangles that
share a side with `b^2`, and the small square in the opposite corner. Thus it's
equal to `(a - b) * b + (a - b) * b + (a - b)^2`. Factor out `(a - b)` and
simplify to obtain `(a - b) * (a + b)`.

**Proof intuition**: It's easier to prove the equivalence by multiplying out
the factors, so reverse the direction of the `calc` block. Then use algebra to
distribute terms and simplify.
-/
theorem factor_diff_squares {a b : ℤ} : a^2 - b^2 ≃ (a - b) * (a + b) := by
  apply Rel.symm
  have pow_two_symm {x : ℤ} : x * x ≃ x^2 := Rel.symm Natural.pow_two
  calc
    _ = (a - b) * (a + b)             := rfl
    _ ≃ a * (a + b) - b * (a + b)     := AA.distribR
    _ ≃ a * a + a * b - b * (a + b)   := sub_substL AA.distribL
    _ ≃ a^2 + a * b - b * (a + b)     := sub_substL (AA.substL pow_two_symm)
    _ ≃ a^2 + a * b - (a + b) * b     := sub_substR AA.comm
    _ ≃ a^2 + a * b - (a * b + b * b) := sub_substR AA.distribR
    _ ≃ a^2 + a * b - (a * b + b^2)   := sub_substR (AA.substR pow_two_symm)
    _ ≃ a^2 + (a * b - (a * b + b^2)) := sub_assoc_addL
    _ ≃ a^2 + ((a * b - a * b) - b^2) := AA.substR (Rel.symm sub_assoc_subR)
    _ ≃ a^2 + (0 - b^2)               := AA.substR (AA.substL sub_same)
    _ ≃ a^2 + (-b^2)                  := AA.substR sub_identL
    _ ≃ a^2 - b^2                     := Rel.symm sub_defn

/--
Zero, one, and negative one are the only integers that are identical to their
cubes.

**Property intuition**: The cubes of integers less than negative one or greater
than one will have absolute value greater than one. Negative one squared is
one, so adding another factor of `-1` to cube it makes the result negative one
as well. Zero and one stay the same when raised to any positive power.

**Proof intuition**: Rearrange `a^3 ≃ a` as `a^3 - a ≃ 0`. Factor the left hand
side into `a * (a - 1) * (a + 1)` using algebra and `factor_diff_squares`. Then
apply `mul_split_zero` twice and rearrange to get the result.
-/
theorem cube_idemp_reasons {a : ℤ} : a^3 ≃ a ↔ a ≃ 0 ∨ a ≃ 1 ∨ a ≃ -1 := by
  have : a^3 ≃ a * a^2 := calc
    _ = a^3        := rfl
    _ ≃ a^(step 2) := Natural.pow_substR Natural.literal_step
    _ ≃ a^2 * a    := Natural.pow_step
    _ ≃ a * a^2    := AA.comm
  have : a ≃ a * 1^2 := calc
    _ = a       := rfl
    _ ≃ a * 1   := Rel.symm AA.identR
    _ ≃ a * 1^2 := AA.substR (Rel.symm Natural.pow_absorbL)
  have factor : a * a^2 - a * 1^2 ≃ a * ((a - 1) * (a + 1)) := calc
    _ = a * a^2 - a * 1^2       := rfl
    _ ≃ a * (a^2 - 1^2)         := Rel.symm mul_distribL_sub
    _ ≃ a * ((a - 1) * (a + 1)) := AA.substR factor_diff_squares
  have : a + 1 ≃ 0 ↔ a ≃ -1 := calc
    _ ↔ a + 1 ≃ 0 := Iff.rfl
    _ ↔ a ≃ 0 - 1 := subR_moveL_addR.symm
    _ ↔ a ≃ -1    := AA.eqv_substR_iff sub_identL
  have nonzero_values : (a - 1) * (a + 1) ≃ 0 ↔ a ≃ 1 ∨ a ≃ -1 := calc
    _ ↔ (a - 1) * (a + 1) ≃ 0 := Iff.rfl
    _ ↔ a - 1 ≃ 0 ∨ a + 1 ≃ 0 := mul_split_zero
    _ ↔ a ≃ 1 ∨ a + 1 ≃ 0     := iff_subst_covar or_mapL zero_diff_iff_eqv
    _ ↔ a ≃ 1 ∨ a ≃ -1        := iff_subst_covar or_mapR ‹a + 1 ≃ 0 ↔ a ≃ -1›
  calc
    _ ↔ a^3 ≃ a                       := Iff.rfl
    _ ↔ a * a^2 ≃ a                   := AA.eqv_substL_iff ‹a^3 ≃ a * a^2›
    _ ↔ a * a^2 ≃ a * 1^2             := AA.eqv_substR_iff ‹a ≃ a * 1^2›
    _ ↔ a * a^2 - a * 1^2 ≃ 0         := zero_diff_iff_eqv.symm
    _ ↔ a * ((a - 1) * (a + 1)) ≃ 0   := AA.eqv_substL_iff factor
    _ ↔ a ≃ 0 ∨ (a - 1) * (a + 1) ≃ 0 := mul_split_zero
    _ ↔ a ≃ 0 ∨ a ≃ 1 ∨ a ≃ -1        := iff_subst_covar or_mapR nonzero_values

/--
Cubing the sign of an integer has no effect.

**Property and proof intuition**: An integer's sign can only be zero, one, or
negative one. All three of those numbers remain the same when cubed, by
`cube_idemp_reasons`.
-/
theorem sgn_cubed {a : ℤ} : (sgn a)^3 ≃ sgn a := by
  have : sgn a ≃ 0 ∨ sgn a ≃ 1 ∨ sgn a ≃ -1 := match sgn_trichotomy a with
  | AA.OneOfThree₁.first (_ : sgn a ≃ 0) =>
    Or.inl ‹sgn a ≃ 0›
  | AA.OneOfThree₁.second (_ : sgn a ≃ 1) =>
    Or.inr (Or.inl ‹sgn a ≃ 1›)
  | AA.OneOfThree₁.third (_ : sgn a ≃ -1) =>
    Or.inr (Or.inr ‹sgn a ≃ -1›)
  have : (sgn a)^3 ≃ sgn a := cube_idemp_reasons.mpr this
  exact this

def sum_sub_err (a b : ℤ) : ℤ := a + b - a * b^2

/-- TODO -/
theorem sgn_sum_pos_prod
    {a b : ℤ} : a * b > 0 → sgn (a + b) ≃ sum_sub_err (sgn a) (sgn b)
    := by
  intro (_ : a * b > 0)
  show sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
  have (And.intro (_ : sgn a ≃ sgn b) _) :=
    mul_gt_zero_iff_sgn_same.mp ‹a * b > 0›
  have sum_same {x y : ℤ} : x ≃ y → sum_sub_err x y ≃ y + y - y^3 := by
    intro (_ : x ≃ y)
    show sum_sub_err x y ≃ y + y - y^3
    have : x * y^2 ≃ y^3 := calc
      _ = x * y^2    := rfl
      _ ≃ y * y^2    := AA.substL ‹x ≃ y›
      _ ≃ y^2 * y    := AA.comm
      _ ≃ y^(step 2) := Rel.symm Natural.pow_step
      _ ≃ y^3        := Natural.pow_substR (Rel.symm Natural.literal_step)
    calc
      _ = sum_sub_err x y := rfl
      _ = x + y - x * y^2 := rfl
      _ ≃ y + y - x * y^2 := sub_substL (AA.substL ‹x ≃ y›)
      _ ≃ y + y - y^3     := sub_substR ‹x * y^2 ≃ y^3›
  let s := sum_sub_err (sgn a) (sgn b)
  have : s ≃ sgn b := calc
    _ = s                                   := rfl
    _ = sgn a + sgn b - (sgn a) * (sgn b)^2 := rfl
    _ ≃ sgn b + sgn b - (sgn b)^3           := sum_same ‹sgn a ≃ sgn b›
    _ ≃ sgn b + sgn b - sgn b               := sub_substR sgn_cubed
    _ ≃ sgn b + (sgn b - sgn b)             := sub_assoc_addL
    _ ≃ sgn b + 0                           := AA.substR sub_same
    _ ≃ sgn b                               := AA.identR
  have : sgn b ≃ s := Rel.symm ‹s ≃ sgn b›
  have : sgn a ≃ s := Rel.trans ‹sgn a ≃ sgn b› ‹sgn b ≃ s›
  have : sgn (a + b) ≃ s := add_preserves_sign ‹sgn a ≃ s› ‹sgn b ≃ s›
  exact this

/-- TODO -/
theorem sgn_sum_zero_prod
    {a b : ℤ} : a * b ≃ 0 → sgn (a + b) ≃ sum_sub_err (sgn a) (sgn b)
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
    {a b : ℤ} : a * b ≥ 0 → sgn (a + b) ≃ sum_sub_err (sgn a) (sgn b)
    := by
  intro (_ : a * b ≥ 0)
  show sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
  have : a * b > 0 ∨ a * b ≃ 0 := ge_split.mp ‹a * b ≥ 0›
  exact match this with
  | Or.inl (_ : a * b > 0) =>
    sgn_sum_pos_prod ‹a * b > 0›
  | Or.inr (_ : a * b ≃ 0) =>
    sgn_sum_zero_prod ‹a * b ≃ 0›

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

/-- TODO -/
theorem sgn_diff_pow_pos
    {a b : ℤ} {n : ℕ} : a ≥ 0 → b ≥ 0 → n ≥ 1 → sgn (a^n - b^n) ≃ sgn (a - b)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0) (_ : n ≥ 1)
  show sgn (a^n - b^n) ≃ sgn (a - b)

  let motive := λ (x : ℕ) => sgn (a^x - b^x) ≃ sgn (a - b)
  have motive_subst {x₁ x₂ : ℕ} : x₁ ≃ x₂ → motive x₁ → motive x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : sgn (a^x₁ - b^x₁) ≃ sgn (a - b))
    show sgn (a^x₂ - b^x₂) ≃ sgn (a - b)
    have pow_substR {c : ℤ} : c^x₂ ≃ c^x₁ :=
      Natural.pow_substR (Rel.symm ‹x₁ ≃ x₂›)
    calc
      _ = sgn (a^x₂ - b^x₂) := rfl
      _ ≃ sgn (a^x₁ - b^x₂) := sgn_subst (sub_substL pow_substR)
      _ ≃ sgn (a^x₁ - b^x₁) := sgn_subst (sub_substR pow_substR)
      _ ≃ sgn (a - b)       := ‹sgn (a^x₁ - b^x₁) ≃ sgn (a - b)›

  apply Natural.ind_from motive_subst ‹n ≥ 1›
  case base =>
    show sgn (a^1 - b^1) ≃ sgn (a - b)
    calc
      _ = sgn (a^1 - b^1) := rfl
      _ ≃ sgn (a - b^1)   := sgn_subst (sub_substL Natural.pow_one)
      _ ≃ sgn (a - b)     := sgn_subst (sub_substR Natural.pow_one)
  case next =>
    intro (m : ℕ) (_ : m ≥ 1) (ih : sgn (a^m - b^m) ≃ sgn (a - b))
    show sgn (a^(step m) - b^(step m)) ≃ sgn (a - b)

    have sub_to_sum
        {w x y z : ℤ} : w*x - y*z ≃ w * (x - z) + (w - y) * z
        := calc
      _ = w*x - y*z                 := rfl
      _ ≃ (w*x - w*z) + (w*z - y*z) := Rel.symm add_sub_telescope
      _ ≃ w * (x - z) + (w*z - y*z) := AA.substL (Rel.symm AA.distribL)
      _ ≃ w * (x - z) + (w - y) * z := AA.substR (Rel.symm AA.distribR)
    have factor_sumL : sgn (a^m * (a - b)) ≃ sgn (a - b) * sgn (a^m) := calc
      _ = sgn (a^m * (a - b))     := rfl
      _ ≃ sgn (a^m) * sgn (a - b) := sgn_compat_mul
      _ ≃ sgn (a - b) * sgn (a^m) := AA.comm
    have factor_sumR : sgn ((a^m - b^m) * b) ≃ sgn (a - b) * sgn b := calc
      _ = sgn ((a^m - b^m) * b)   := rfl
      _ ≃ sgn (a^m - b^m) * sgn b := sgn_compat_mul
      _ ≃ sgn (a - b) * sgn b     := AA.substL ih
    have : (sgn a)^2 ≃ sgn a := sgn_sqr_nonneg.mpr ‹a ≥ 0›
    have : sgn (a^m) ≃ sgn a := calc
      _ = sgn (a^m) := rfl
      _ ≃ (sgn a)^m := sgn_pow
      _ ≃ sgn a     := pow_absorbL ‹m ≥ 1› ‹(sgn a)^2 ≃ sgn a›
    let sab := sgn (a - b)
    let sam := sgn (a^m)
    let amab := a^m * (a - b)
    let abmb := (a^m - b^m) * b
    have : a * b ≥ 0 := mul_preserves_nonneg ‹a ≥ 0› ‹b ≥ 0›
    have : sgn (a * b) ≥ 0 := sgn_preserves_ge_zero.mp ‹a * b ≥ 0›
    have : sab^2 * sgn (a * b) ≥ 0 :=
      mul_preserves_nonneg sqr_nonneg ‹sgn (a * b) ≥ 0›
    have : sgn (amab * abmb) ≥ 0 := calc
      _ = sgn (amab * abmb)           := rfl
      _ ≃ sgn amab * sgn abmb         := sgn_compat_mul
      _ ≃ (sab * sam) * sgn abmb      := AA.substL factor_sumL
      _ ≃ (sab * sam) * (sab * sgn b) := AA.substR factor_sumR
      _ ≃ (sab * sab) * (sam * sgn b) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ sab^2 * (sam * sgn b)       := AA.substL (Rel.symm Natural.pow_two)
      _ ≃ sab^2 * (sgn a * sgn b)     := AA.substR (AA.substL ‹sam ≃ sgn a›)
      _ ≃ sab^2 * sgn (a * b)         := AA.substR (Rel.symm sgn_compat_mul)
      _ ≥ 0                           := ‹sab^2 * sgn (a * b) ≥ 0›
    have terms_mul_nonneg : amab * abmb ≥ 0 := sgn_preserves_ge_zero.mpr this
    have reduce : sum_sub_err (sgn (a^m)) (sgn b) ≃ sgn (a + b) := calc
      _ = sum_sub_err (sgn (a^m)) (sgn b) := rfl
      _ ≃ sum_sub_err (sgn a) (sgn b)     := sse_substL ‹sgn (a^m) ≃ sgn a›
      _ ≃ sgn (a + b)                     := Rel.symm (sgn_sum ‹a * b ≥ 0›)
    have : a + b ≥ 0 := calc
      _ = a + b := rfl
      _ ≥ 0 + b := ge_addR.mp ‹a ≥ 0›
      _ ≥ 0 + 0 := ge_addL.mp ‹b ≥ 0›
      _ ≃ 0     := AA.identL
    have : a + b > 0 ∨ a + b ≃ 0 := ge_split.mp ‹a + b ≥ 0›
    have : sgn (a - b) ≃ 0 ∨ sgn (a + b) ≃ 1 := match this with
    | Or.inl (_ : a + b > 0) =>
      have : sgn (a + b) ≃ 1 := gt_zero_sgn.mp ‹a + b > 0›
      Or.inr ‹sgn (a + b) ≃ 1›
    | Or.inr (_ : a + b ≃ 0) =>
      have (And.intro (_ : a ≃ 0) (_ : b ≃ 0)) :=
        (zero_sum_split ‹a ≥ 0› ‹b ≥ 0›).mp ‹a + b ≃ 0›
      have : sgn (a - b) ≃ 0 := calc
        _ = sgn (a - b)     := rfl
        _ ≃ sgn (0 - b)     := sgn_subst (sub_substL ‹a ≃ 0›)
        _ ≃ sgn ((0:ℤ) - 0) := sgn_subst (sub_substR ‹b ≃ 0›)
        _ ≃ sgn (0:ℤ)       := sgn_subst sub_same
        _ ≃ 0               := sgn_zero.mp Rel.refl
      Or.inl ‹sgn (a - b) ≃ 0›
    have expand
        : a^(step m) - b^(step m) ≃ a^m * (a - b) + (a^m - b^m) * b
        := calc
      _ = a^(step m) - b^(step m)         := rfl
      _ ≃ a^m * a - b^(step m)            := sub_substL Natural.pow_step
      _ ≃ a^m * a - b^m * b               := sub_substR Natural.pow_step
      _ ≃ a^m * (a - b) + (a^m - b^m) * b := sub_to_sum
    have factor_sgn_sum : sgn (amab + abmb) ≃ sgn (a-b) * sgn (a+b) := calc
      _ = sgn (amab + abmb)                     := rfl
      _ ≃ sum_sub_err (sgn amab) (sgn abmb)     := sgn_sum terms_mul_nonneg
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

/--
The ordering of two nonnegative integers, each raised to the same natural
number power (`sgn (a^n - b^n)`), is exactly the product of the ordering of the
original integers with the sign of the power.

**Property and proof intuition**: The power is either zero or positive. If it's
zero, then both sides of the equivalence are zero. If it's positive, then by
`sgn_diff_pow_pos` the powers can be dropped, and `sgn (n:ℤ)` can be included
because it's equivalent to one.
-/
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
    have : a^n - b^n ≃ 0 := calc
      _ = a^n - b^n := rfl
      _ ≃ a^0 - b^n := sub_substL (Natural.pow_substR ‹n ≃ 0›)
      _ ≃ a^0 - b^0 := sub_substR (Natural.pow_substR ‹n ≃ 0›)
      _ ≃ 1 - b^0   := sub_substL Natural.pow_zero
      _ ≃ (1:ℤ) - 1 := sub_substR Natural.pow_zero
      _ ≃ 0         := sub_same
    have : sgn (n:ℤ) ≃ 0 := calc
      _ = sgn (n:ℤ)     := rfl
      _ ≃ sgn ((0:ℕ):ℤ) := sgn_subst (AA.subst₁ ‹n ≃ 0›)
      _ ≃ 0             := sgn_zero.mp Rel.refl
    calc
      _ = sgn (a^n - b^n)         := rfl
      _ ≃ sgn (0:ℤ)               := sgn_subst ‹a^n - b^n ≃ 0›
      _ ≃ 0                       := sgn_zero.mp Rel.refl
      _ ≃ sgn (a - b) * 0         := Rel.symm AA.absorbR
      _ ≃ sgn (a - b) * sgn (n:ℤ) := AA.substR (Rel.symm ‹sgn (n:ℤ) ≃ 0›)
  | Or.inr (_ : n > 0) =>
    have : Positive n := Natural.lt_zero_pos.mpr ‹n > 0›
    have : n ≥ 1 := Natural.positive_ge.mp ‹Positive n›
    have : Positive (n:ℤ) := positive_intro_nat ‹Positive n› Rel.refl
    have : sgn (n:ℤ) ≃ 1 := sgn_positive.mp ‹Positive (n:ℤ)›
    calc
      _ = sgn (a^n - b^n)         := rfl
      _ ≃ sgn (a - b)             := sgn_diff_pow_pos ‹a ≥ 0› ‹b ≥ 0› ‹n ≥ 1›
      _ ≃ sgn (a - b) * 1         := Rel.symm AA.identR
      _ ≃ sgn (a - b) * sgn (n:ℤ) := AA.substR (Rel.symm ‹sgn (n:ℤ) ≃ 1›)

end Lean4Axiomatic.Integer
