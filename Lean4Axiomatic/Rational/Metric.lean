import Lean4Axiomatic.Metric
import Lean4Axiomatic.Rational.Order

/-! # Rational numbers: metric functions -/

namespace Lean4Axiomatic.Rational

open Metric (abs dist MetricSpace)
open Signed (sgn)

/-! ## Axioms -/

/-- Operations pertaining to metrics on rational numbers. -/
class Metric.Ops (ℚ : Type) :=
  /-- Absolute value. -/
  _abs : ℚ → ℚ

  /-- Distance. -/
  _dist : ℚ → ℚ → ℚ

/-- Enables the use of the standard names for absolute value and distance. -/
instance metric_space_inst {ℚ : Type} [Metric.Ops ℚ] : MetricSpace ℚ := {
  abs := Metric.Ops._abs
  dist := Metric.Ops._dist
}

/-- Properties of rational number metrics. -/
class Metric.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Ops ℚ]
    :=
  /--
  The absolute value of a rational number is equivalent to the product of that
  number with its sign.
  -/
  abs_sgn {p : ℚ} : abs p ≃ p * sgn p

  /--
  The distance between two rational numbers is the absolute value of their
  difference.
   -/
  dist_abs {p q : ℚ} : dist p q ≃ abs (p - q)

export Metric.Props (abs_sgn dist_abs)

/-- All rational number metric axioms. -/
class Metric
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ]
    :=
  toOps : Metric.Ops ℚ
  toProps : Metric.Props ℚ

attribute [instance] Metric.toOps
attribute [instance] Metric.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ] [Subtraction ℚ]
  [Multiplication ℚ] [Reciprocation ℚ] [Division ℚ]
  [Sign ℚ] [Order ℚ] [Metric ℚ]

/--
The absolute value function preserves equivalence over its argument.

**Property intuition**: This must be the case for `abs` to be a function.

**Proof intuition**: Expand `abs` into its `sgn` definition, and use
substitution on multiplication and `sgn`.
-/
theorem abs_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → abs p₁ ≃ abs p₂ := by
  intro (_ : p₁ ≃ p₂)
  show abs p₁ ≃ abs p₂
  calc
    abs p₁      ≃ _ := abs_sgn
    p₁ * sgn p₁ ≃ _ := mul_substL ‹p₁ ≃ p₂›
    p₂ * sgn p₁ ≃ _ := mul_substR (from_integer_subst (sgn_subst ‹p₁ ≃ p₂›))
    p₂ * sgn p₂ ≃ _ := eqv_symm abs_sgn
    abs p₂      ≃ _ := eqv_refl

/--
The sign of a rational number's absolute value is the squared sign of the
rational number.

**Property and proof intuition**: The absolute value of a number is that number
times its sign; taking the `sgn` of that gives the result.
-/
theorem sgn_abs {p : ℚ} : sgn (abs p) ≃ sgn p * sgn p := calc
  sgn (abs p)             ≃ _ := sgn_subst abs_sgn
  sgn (p * sgn p)         ≃ _ := sgn_compat_mul
  sgn p * sgn (sgn p : ℚ) ≃ _ := AA.substR sgn_from_integer
  sgn p * sgn (sgn p)     ≃ _ := AA.substR sgn_idemp
  sgn p * sgn p           ≃ _ := Rel.refl

/--
Zero is the only rational number that has an absolute value of zero.

**Property intuition**: This fits the description of absolute value as
"distance from zero".

**Proof intuition**: In the forward direction, `abs p` expands to `p * sgn p`;
both factors imply that `p ≃ 0`. In the reverse direction, `p * sgn p` is
trivially zero when `p` is.
-/
theorem abs_zero {p : ℚ} : abs p ≃ 0 ↔ p ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : abs p ≃ 0)
    show p ≃ 0
    have : p * sgn p ≃ 0 := AA.eqv_substL abs_sgn ‹abs p ≃ 0›
    have : p ≃ 0 ∨ (sgn p : ℚ) ≃ 0 := mul_split_zero.mp this
    match this with
    | Or.inl (_ : p ≃ 0) =>
      exact ‹p ≃ 0›
    | Or.inr (_ : (sgn p : ℚ) ≃ 0) =>
      have : sgn p ≃ 0 := from_integer_inject ‹(sgn p : ℚ) ≃ 0›
      have : p ≃ 0 := sgn_zero.mpr this
      exact this
  case mpr =>
    intro (_ : p ≃ 0)
    show abs p ≃ 0
    calc
      abs p           ≃ _ := abs_sgn
      p * sgn p       ≃ _ := mul_substL ‹p ≃ 0›
      (0 : ℚ) * sgn p ≃ _ := mul_absorbL
      0               ≃ _ := eqv_refl

/--
A positive rational number's absolute value is itself.

**Property intuition**: Absolute value measures "distance from zero" using
positive numbers, so a positive input is already in the right form.

**Proof intuition**: Follows from the `sgn` representation of `abs` because a
positive number's sign is one.
-/
theorem abs_positive {p : ℚ} : sgn p ≃ 1 → abs p ≃ p := by
  intro (_ : sgn p ≃ 1)
  show abs p ≃ p
  calc
    _ ≃ abs p     := eqv_refl
    _ ≃ p * sgn p := abs_sgn
    _ ≃ p * 1     := mul_substR (from_integer_subst ‹sgn p ≃ 1›)
    _ ≃ p         := mul_identR

/--
A negative rational number's absolute value is its negation.

**Property intuition**: Absolute value measures "distance from zero" using
positive numbers, so a negative input just needs to be negated to put it into
the right form.

**Proof intuition**: Follows from the `sgn` representation of `abs` because a
negative number's sign is negative one.
-/
theorem abs_negative {p : ℚ} : sgn p ≃ -1 → abs p ≃ -p := by
  intro (_ : sgn p ≃ -1)
  show abs p ≃ -p
  have : (sgn p : ℚ) ≃ -1 := calc
    _ ≃ (sgn p : ℚ)    := eqv_refl
    _ ≃ ((-1 : ℤ) : ℚ) := from_integer_subst ‹sgn p ≃ -1›
    _ ≃ -((1 : ℤ) : ℚ) := neg_compat_from_integer
    _ ≃ -1             := eqv_refl
  have : abs p ≃ -p := calc
    _ ≃ abs p     := eqv_refl
    _ ≃ p * sgn p := abs_sgn
    _ ≃ p * -1    := mul_substR ‹(sgn p : ℚ) ≃ -1›
    _ ≃ -1 * p    := mul_comm
    _ ≃ -p        := mul_neg_one
  exact this

/--
Every rational number's absolute value is either itself, or its negation.

**Property and proof intuition**: Every rational number is either zero,
positive, or negative. The positive and negative cases are clear. Zero fits
both categories, so the result holds either way.
-/
theorem abs_cases {p : ℚ} : abs p ≃ p ∨ abs p ≃ -p := by
  have : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1) := sgn_trichotomy p
  match this with
  | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
    have : p ≃ 0 := sgn_zero.mpr ‹sgn p ≃ 0›
    have : abs p ≃ p := calc
      _ ≃ abs p := eqv_refl
      _ ≃ 0     := abs_zero.mpr ‹p ≃ 0›
      _ ≃ p     := eqv_symm ‹p ≃ 0›
    exact (Or.inl this)
  | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
    have : abs p ≃ p := abs_positive ‹sgn p ≃ 1›
    exact (Or.inl this)
  | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
    have : abs p ≃ -p := abs_negative ‹sgn p ≃ -1›
    exact (Or.inr this)

/--
The absolute value of a rational number is greater than or equivalent to zero.

**Property intuition**: The absolute value discards the sign of a number and
returns the magnitude, so we'd expect it to be nonnegative.

**Proof intuition**: The sign of a rational number's absolute value is that
number's sign squared. A square can never be negative, thus the absolute value
must be positive or zero.
-/
theorem abs_ge_zero {p : ℚ} : abs p ≥ 0 := by
  have : sgn (p * p) ≃ sgn (abs p) := calc
    _ ≃ sgn (p * p)   := Rel.refl
    _ ≃ sgn p * sgn p := sgn_compat_mul
    _ ≃ sgn (abs p)   := Rel.symm sgn_abs
  have : sgn (abs p) ≄ -1 := AA.neqv_substL this nonneg_square
  have : abs p ≥ 0 := ge_zero_sgn.mpr this
  exact this

/--
A rational number is always less than or equivalent to its absolute value.

This lemma is useful for the proof of `abs_upper_bound`.

**Property intuition**: All absolute values are nonnegative, so negative
numbers are definitely less than their absolute values. Nonnegative numbers are
equivalent to theirs.

**Proof intuition**: Every rational number `p` can be represented as
`p * sgn 1`. This is always less than or equivalent to `p * sgn p ≃ abs p`.
-/
theorem abs_ge_self {p : ℚ} : abs p ≥ p := by
  show p ≤ abs p
  calc
    _ ≃ p               := eqv_refl
    _ ≃ p * 1           := eqv_symm mul_identR
    _ ≃ p * sgn (1 : ℚ) := mul_substR (from_integer_subst (Rel.symm sgn_one))
    _ ≤ p * sgn p       := mul_sgn_self_max
    _ ≃ abs p           := eqv_symm abs_sgn

/--
A rational number is always greater than or equivalent to the negation of its
absolute value.

This lemma is useful for the proof of `abs_upper_bound`.

**Property intuition**: All absolute values are nonnegative, so their negations
are nonpositive. Thus all positive numbers are definitely greater than their
negated absolute values. Nonpositive numbers are equivalent to theirs.

**Proof intuition**: Every negated rational number `-p` can be represented as
`p * sgn (-1)`. This is always less than or equivalent to `p * sgn p ≃ abs p`.
Negating both sides of that ordering gives us the result.
-/
theorem neg_abs_le_self {p : ℚ} : -abs p ≤ p := by
  have : (sgn (-1 : ℚ) : ℚ) ≃ -1 := calc
    _ ≃ (sgn (-1 : ℚ) : ℚ) := eqv_refl
    _ ≃ ((-1 : ℤ) : ℚ)     := from_integer_subst sgn_neg_one
    _ ≃ (-1)               := neg_compat_from_integer
  have : -p ≤ abs p := calc
    _ ≃ -p               := eqv_refl
    _ ≃ (-1) * p         := eqv_symm mul_neg_one
    _ ≃ p * (-1)         := mul_comm
    _ ≃ p * sgn (-1 : ℚ) := mul_substR (eqv_symm this)
    _ ≤ p * sgn p        := mul_sgn_self_max
    _ ≃ abs p            := eqv_symm abs_sgn
  have : -abs p ≤ p := calc
    _ ≃ -abs p := eqv_refl
    _ ≤ -(-p)  := le_subst_neg ‹-p ≤ abs p›
    _ ≃ p      := neg_involutive
  exact this

/--
Convert between an inequality on the absolute value of a rational number and
inequalities on the rational number itself.

**Property intuition**: Viewing the absolute value as the "distance from zero",
if a rational number's absolute value is below some quantity, that's equivalent
to the underlying rational number being within that quantity of zero, in either
the positive or negative direction.

**Proof intuition**: Not much to provide aside from just reading the proof; it
seems to require handling "positive" and "negative" cases separately.
-/
theorem abs_upper_bound {p q : ℚ} : abs p ≤ q ↔ -q ≤ p ∧ p ≤ q := by
  apply Iff.intro
  case mp =>
    intro (_ : abs p ≤ q)
    show -q ≤ p ∧ p ≤ q
    have : -q ≤ p := calc
      _ ≃ -q       := eqv_refl
      _ ≤ (-abs p) := le_subst_neg ‹abs p ≤ q›
      _ ≤ p        := neg_abs_le_self
    have : p ≤ q := calc
      _ ≃ p     := eqv_refl
      _ ≤ abs p := abs_ge_self
      _ ≤ q     := ‹abs p ≤ q›
    exact And.intro ‹-q ≤ p› ‹p ≤ q›
  case mpr =>
    intro (And.intro (_ : -q ≤ p) (_ : p ≤ q))
    show abs p ≤ q
    have : abs p ≃ p ∨ abs p ≃ -p := abs_cases
    match this with
    | Or.inl (_ : abs p ≃ p) =>
      calc
        _ ≃ abs p := eqv_refl
        _ ≃ p     := ‹abs p ≃ p›
        _ ≤ q     := ‹p ≤ q›
    | Or.inr (_ : abs p ≃ -p) =>
      calc
        _ ≃ abs p   := eqv_refl
        _ ≃ (-p)    := ‹abs p ≃ -p›
        _ ≤ (-(-q)) := le_subst_neg ‹-q ≤ p›
        _ ≃ q       := neg_involutive

/--
The [triangle inequality](https://w.wiki/6VUr); i.e. how absolute value behaves
over addition.

**Property intuition**: The sum of two absolute values will always be
non-negative, while the sum of any two rationals can have smaller magnitude due
to negative values.

**Proof intuition**: Expand `abs` in terms of `sgn`. The key substitution is
that a rational number times an arbitrary sign value will never be greater than
that rational number times its own sign, i.e. the number's absolute value.
-/
theorem abs_compat_add {p q : ℚ} : abs (p + q) ≤ abs p + abs q := calc
  _ ≃ abs (p + q)                       := eqv_refl
  _ ≃ (p + q) * sgn (p + q)             := abs_sgn
  _ ≃ p * sgn (p + q) + q * sgn (p + q) := mul_distribR
  _ ≤ p * sgn p + q * sgn (p + q)       := le_substL_add mul_sgn_self_max
  _ ≤ p * sgn p + q * sgn q             := le_substR_add mul_sgn_self_max
  _ ≃ abs p + q * sgn q                 := add_substL (eqv_symm abs_sgn)
  _ ≃ abs p + abs q                     := add_substR (eqv_symm abs_sgn)

/--
A rational number product's absolute value is the product of the absolute
values of its factors.

**Property intuition**: The magnitude of a product is the same regardless of
the signs of its factors.

**Proof intuition**: Expand `abs (p * q)` into its `sgn` representation.
Regroup the factors so that `abs p` and `abs q` are separate.
-/
theorem abs_compat_mul {p q : ℚ} : abs (p * q) ≃ abs p * abs q := by
  have : (sgn (p * q) : ℚ) ≃ (sgn p : ℚ) * (sgn q : ℚ) := calc
    _ ≃ (sgn (p * q) : ℚ)         := eqv_refl
    _ ≃ ((sgn p * sgn q : ℤ) : ℚ) := from_integer_subst sgn_compat_mul
    _ ≃ (sgn p : ℚ) * (sgn q : ℚ) := mul_compat_from_integer
  have : abs (p * q) ≃ abs p * abs q := calc
    _ ≃ abs (p * q)                           := eqv_refl
    _ ≃ (p * q) * (sgn (p * q) : ℚ)           := abs_sgn
    _ ≃ (p * q) * ((sgn p : ℚ) * (sgn q : ℚ)) := mul_substR this
    _ ≃ (p * sgn p) * (q * sgn q)             := AA.expr_xxfxxff_lr_swap_rl
    _ ≃ abs p * (q * sgn q)                   := mul_substL (eqv_symm abs_sgn)
    _ ≃ abs p * abs q                         := mul_substR (eqv_symm abs_sgn)
  exact this

/--
The absolute values of a rational number and its negation are the same.

**Property intuition**: Absolute value discards the sign of a number.

**Proof intuition**: Expand negation into multiplication by `-1`, then use
`abs_compat_mul` to split into a product of absolute values and simplify.
-/
theorem abs_absorb_neg {p : ℚ} : abs (-p) ≃ abs p := calc
  _ ≃ abs (-p)         := eqv_refl
  _ ≃ abs (-1 * p)     := abs_subst (eqv_symm mul_neg_one)
  _ ≃ abs (-1) * abs p := abs_compat_mul
  _ ≃ -(-1) * abs p    := mul_substL (abs_negative sgn_neg_one)
  _ ≃ 1 * abs p        := mul_substL neg_involutive
  _ ≃ abs p            := mul_identL

/--
Distance between rational numbers is preserved if the left argument is replaced
with an equivalent value.

**Property intuition**: This must be true for `dist` to be a function.

**Proof intuition**: Expand `dist` into its `abs` representation. The left
argument can be substituted under `abs` and subtraction.
-/
theorem dist_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → dist p₁ q ≃ dist p₂ q := by
  intro (_ : p₁ ≃ p₂)
  show dist p₁ q ≃ dist p₂ q
  calc
    _ ≃ dist p₁ q    := eqv_refl
    _ ≃ abs (p₁ - q) := dist_abs
    _ ≃ abs (p₂ - q) := abs_subst (sub_substL ‹p₁ ≃ p₂›)
    _ ≃ dist p₂ q    := eqv_symm dist_abs

/--
Distance between rational numbers is preserved if the right argument is
replaced with an equivalent value.

**Property intuition**: This must be true for `dist` to be a function.

**Proof intuition**: Expand `dist` into its `abs` representation. The right
argument can be substituted under `abs` and subtraction.
-/
theorem dist_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → dist q p₁ ≃ dist q p₂ := by
  intro (_ : p₁ ≃ p₂)
  show dist q p₁ ≃ dist q p₂
  calc
    _ ≃ dist q p₁    := eqv_refl
    _ ≃ abs (q - p₁) := dist_abs
    _ ≃ abs (q - p₂) := abs_subst (sub_substR ‹p₁ ≃ p₂›)
    _ ≃ dist q p₂    := eqv_symm dist_abs

/--
The distance between two rational numbers is always zero or greater.

**Property intuition**: Distance measures how "far apart" two numbers are. It's
not possible for numbers to be closer than zero distance.

**Proof intutition**: Distance is defined as an absolute value, which is also
guaranteed to be nonnegative.
-/
theorem dist_ge_zero {p q : ℚ} : dist p q ≥ 0 := calc
  _ ≃ dist p q    := eqv_refl
  _ ≃ abs (p - q) := dist_abs
  _ ≥ 0           := abs_ge_zero

/--
Equivalent rational numbers are the only ones that can be a distance of zero
apart.

**Property intuition**: Distinct numbers have a nonzero separation.

**Proof intuition**: In both directions, use properties of `abs` and
subtraction when their results are zero.
-/
theorem dist_zero {p q : ℚ} : dist p q ≃ 0 ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : dist p q ≃ 0)
    show p ≃ q
    have : abs (p - q) ≃ 0 := AA.eqv_substL dist_abs ‹dist p q ≃ 0›
    have : p - q ≃ 0 := abs_zero.mp this
    have : p ≃ q := sub_eqv_zero_iff_eqv.mp this
    exact this
  case mpr =>
    intro (_ : p ≃ q)
    show dist p q ≃ 0
    calc
      _ ≃ dist p q    := eqv_refl
      _ ≃ abs (p - q) := dist_abs
      _ ≃ abs 0       := abs_subst (sub_eqv_zero_iff_eqv.mpr ‹p ≃ q›)
      _ ≃ 0           := abs_zero.mpr eqv_refl

/--
The arguments to `dist` can be swapped without changing its value (i.e.,
distance is a symmetric function).

**Property intuition**: Distance just measures the magnitude of separation, not
the direction.

**Proof intuition**: Expand distance into the absolute value of the difference;
absolute value absorbs the negation generated by swapping the difference's
operands.
-/
theorem dist_symm {p q : ℚ} : dist p q ≃ dist q p := calc
  _ ≃ dist p q       := eqv_refl
  _ ≃ abs (p - q)    := dist_abs
  _ ≃ abs (-(q - p)) := abs_subst (eqv_symm neg_sub)
  _ ≃ abs (q - p)    := abs_absorb_neg
  _ ≃ dist q p       := eqv_symm dist_abs

end Lean4Axiomatic.Rational
