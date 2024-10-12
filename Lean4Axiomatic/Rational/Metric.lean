import Lean4Axiomatic.Metric
import Lean4Axiomatic.Rational.MinMax

/-! # Rational numbers: metric functions -/

namespace Lean4Axiomatic.Rational

open Logic (AP and_mapL and_mapR iff_subst_covar)
open Metric (abs dist MetricSpace)
open Ordered (max min)
open Rel (iff_subst_eqv)
open Signed (sgn)

/-! ## Axioms -/

/-- Operations pertaining to metrics on rational numbers. -/
class Metric.Ops (ℚ : Type) :=
  /-- Absolute value. -/
  _abs : ℚ → ℚ

  /-- Distance. -/
  _dist : ℚ → ℚ → ℚ

  /-- ε-closeness. -/
  _close : ℚ → ℚ → ℚ → Prop

  /-- Betweenness. -/
  _between : ℚ → ℚ → ℚ → Prop

/-- Enables the use of the standard names for absolute value and distance. -/
instance metric_space_inst {ℚ : Type} [Metric.Ops ℚ] : MetricSpace ℚ := {
  abs := Metric.Ops._abs
  dist := Metric.Ops._dist
}

/--
Mixfix notation for ε-closeness.

Has the same precedence as the equivalence and inequality operators.
-/
notation:50 x:51 " ⊢" ε:51 "⊣ " y:51 => Metric.Ops._close ε x y

/--
Mixfix notation for betweenness.

Has the same precedence as the equivalence and inequality operators.
-/
notation:50 x:51 "⊣ " y:51 " ⊢" z:51 => Metric.Ops._between x y z

/-- Properties of rational number metrics. -/
class Metric.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ] [Ops ℚ]
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

  /-- ε-closeness can be expressed in terms of distance. -/
  close_dist {ε p q : ℚ} : p ⊢ε⊣ q ↔ dist p q ≤ ε

  /--
  Betweenness is expressed as two cases, for the possible orderings of the
  exterior values.
  -/
  between_order {p q r : ℚ} : p⊣ q ⊢r ↔ p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p

export Metric.Props (abs_sgn between_order close_dist dist_abs)

/-- All rational number metric axioms. -/
class Metric
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Order ℚ]
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
  [Sign ℚ] [Order ℚ] [MinMax ℚ] [Metric ℚ]

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
The absolute value of a rational number is nonnegative.

**Property intuition**: The absolute value discards the sign of a number and
returns its magnitude, so we'd expect it to be nonnegative.

**Proof intuition**: The sign of a rational number's absolute value is that
number's sign squared. A square can never be negative, thus the absolute value
must be positive or zero.
-/
theorem abs_nonneg {p : ℚ} : abs p ≥ 0 := by
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
The distance between two rational numbers is always nonnegative.

**Property intuition**: Distance measures how "far apart" two numbers are. It's
not possible for numbers to be closer than zero distance.

**Proof intutition**: Distance is defined as an absolute value, which is also
guaranteed to be nonnegative.
-/
theorem dist_nonneg {p q : ℚ} : dist p q ≥ 0 := calc
  _ ≃ dist p q    := eqv_refl
  _ ≃ abs (p - q) := dist_abs
  _ ≥ 0           := abs_nonneg

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
theorem dist_comm {p q : ℚ} : dist p q ≃ dist q p := calc
  _ ≃ dist p q       := eqv_refl
  _ ≃ abs (p - q)    := dist_abs
  _ ≃ abs (-(q - p)) := abs_subst (eqv_symm neg_sub)
  _ ≃ abs (q - p)    := abs_absorb_neg
  _ ≃ dist q p       := eqv_symm dist_abs

/--
The [triangle inequality for distance](https://w.wiki/6hbw).

**Property intuition**: The direct distance between two numbers is never more
than the distance from one of them, to a third number, then back to the other.

**Proof intuition**: Expand distance into absolute value of a difference; the
result follows from the triangle inequality for absolute value and the
telescoping addition of differences.
-/
theorem dist_triangle {p q r : ℚ} : dist p r ≤ dist p q + dist q r := calc
  _ ≃ dist p q + dist q r       := eqv_refl
  _ ≃ abs (p - q) + dist q r    := add_substL dist_abs
  _ ≃ abs (p - q) + abs (q - r) := add_substR dist_abs
  _ ≥ abs ((p - q) + (q - r))   := abs_compat_add
  _ ≃ abs (p - r)               := abs_subst add_sub_telescope
  _ ≃ dist p r                  := eqv_symm dist_abs

/--
The distance between two values is unchanged after removing a common term added
on their left.

**Property intuition**: The distance between two points is preserved when they
are translated by the same amount.

**Proof intuition**: Expand distance into its absolute value definition, and
simplify.
-/
theorem dist_cancelL_add {p q r : ℚ} : dist (r + p) (r + q) ≃ dist p q := calc
  _ ≃ dist (r + p) (r + q)    := eqv_refl
  _ ≃ abs ((r + p) - (r + q)) := dist_abs
  _ ≃ abs (p - q)             := abs_subst sub_cancelL_add
  _ ≃ dist p q                := eqv_symm dist_abs

/--
The distance between two values is unchanged after removing a common term added
on their right.

**Property intuition**: The distance between two points is preserved when they
are translated by the same amount.

**Proof intuition**: Use commutativity to put the common term on the left, then
invoke the left-handed version of this property.
-/
theorem dist_cancelR_add {p q r : ℚ} : dist (p + r) (q + r) ≃ dist p q := calc
  _ ≃ dist (p + r) (q + r) := eqv_refl
  _ ≃ dist (r + p) (q + r) := dist_substL add_comm
  _ ≃ dist (r + p) (r + q) := dist_substR add_comm
  _ ≃ dist p q             := dist_cancelL_add

/--
Distribute a left multiplicative factor into the distance function's arguments.

**Property intuition**: Scaling the distance between two points by some amount
can be accomplished by scaling the locations of the points by that amount, in
either the positive or negative direction.

**Proof intuition**: Convert distance to absolute value, then transform by
algebraic properties of absolute value and subtraction.
-/
theorem dist_distribL
    {p q r : ℚ} : abs r * dist p q ≃ dist (r * p) (r * q)
    := calc
  _ ≃ abs r * dist p q     := eqv_refl
  _ ≃ abs r * abs (p - q)  := mul_substR dist_abs
  _ ≃ abs (r * (p - q))    := eqv_symm abs_compat_mul
  _ ≃ abs (r * p - r * q)  := abs_subst mul_distribL_sub
  _ ≃ dist (r * p) (r * q) := eqv_symm dist_abs

/--
Distribute a right multiplicative factor into the distance function's
arguments.

**Property intuition**: Scaling the distance between two points by some amount
can be accomplished by scaling the locations of the points by that amount, in
either the positive or negative direction.

**Proof intuition**: Transform the left-handed version of this property using
commutativity of multiplication.
-/
theorem dist_distribR
    {p q r : ℚ} : (dist p q) * abs r ≃ dist (p * r) (q * r)
    := calc
  _ ≃ (dist p q) * abs r := eqv_refl
  _ ≃ abs r * dist p q := mul_comm
  _ ≃ dist (r * p) (r * q) := dist_distribL
  _ ≃ dist (p * r) (r * q) := dist_substL mul_comm
  _ ≃ dist (p * r) (q * r) := dist_substR mul_comm

/--
Drop negations from both of the distance function's arguments.

**Property intuition**: Distance is not directional, so the distance between
negated points is the same as the distance between their un-negated
counterparts.

**Proof intuition**: Special case of distributing a factor (`-1`) into the
distance function's arguments.
-/
theorem dist_cancel_neg {p q : ℚ} : dist (-p) (-q) ≃ dist p q := calc
  _ ≃ dist (-p) (-q)         := eqv_refl
  _ ≃ dist (-1 * p) (-q)     := dist_substL (eqv_symm mul_neg_one)
  _ ≃ dist (-1 * p) (-1 * q) := dist_substR (eqv_symm mul_neg_one)
  _ ≃ abs (-1) * dist p q    := eqv_symm dist_distribL
  _ ≃ abs 1 * dist p q       := mul_substL abs_absorb_neg
  _ ≃ 1 * dist p q           := mul_substL (abs_positive sgn_one)
  _ ≃ dist p q               := mul_identL

/--
Two rational numbers are "at most" a distance of zero apart iff they are
equivalent.

**Property intuition**: If there's no distance between the numbers, they must
be the same.

**Proof intuition**: Expand 0-close into its distance definition and use
properties of order.
-/
theorem close_zero {p q : ℚ} : p ⊢0⊣ q ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p ⊢0⊣ q)
    show p ≃ q
    have : dist p q ≤ 0 := close_dist.mp ‹p ⊢0⊣ q›
    have : dist p q ≥ 0 := dist_nonneg
    have : dist p q ≃ 0 := le_antisymm ‹dist p q ≤ 0› ‹dist p q ≥ 0›
    have : p ≃ q := dist_zero.mp this
    exact this
  case mpr =>
    intro (_ : p ≃ q)
    show p ⊢0⊣ q
    have : dist p q ≃ 0 := dist_zero.mpr ‹p ≃ q›
    have : dist p q ≤ 0 := le_cases.mpr (Or.inr this)
    have : p ⊢0⊣ q := close_dist.mpr this
    exact this

/--
The `ε` in ε-closeness is nonnegative.

**Property and proof intuition**: Distance is nonnegative.
-/
theorem close_nonneg {ε p q : ℚ} : p ⊢ε⊣ q → ε ≥ 0 := by
  intro (_ : p ⊢ε⊣ q)
  show ε ≥ 0
  calc
    _ ≃ ε        := eqv_refl
    _ ≥ dist p q := close_dist.mp ‹p ⊢ε⊣ q›
    _ ≥ 0        := dist_nonneg

/--
Two rational numbers are equivalent exactly when they are closer together than
any positive distance.

**Proof intuition**: In the forward direction, suppose that `dist p q` is
positive (otherwise it's zero, and the claim holds). But then we can supply
half of that distance, which is still positive, to the hypothesis to show that
`p` and `q` must be closer than we assumed: contradiction. The reverse
direction follows immediately from definitions.
-/
theorem close_eqv {p q : ℚ} : ({ε : ℚ} → ε > 0 → p ⊢ε⊣ q) ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (hyp : {ε : ℚ} → ε > 0 → p ⊢ε⊣ q)
    show p ≃ q
    have : dist p q ≥ 0 := dist_nonneg
    have : dist p q > 0 ∨ dist p q ≃ 0 := ge_cases.mp this
    match this with
    | Or.inl (_ : dist p q > 0) =>
      let ε := dist p q
      have : AP ((2:ℚ) ≄ 0) := AP.mk (nonzero_if_pos sgn_two)
      have (And.intro (_ : ε > ε/2) (_ : ε/2 > 0)) := halve ‹ε > 0›
      have : p ⊢ε/2⊣ q := hyp ‹ε/2 > 0›
      have : dist p q ≤ ε/2 := close_dist.mp this
      have : ε ≤ ε/2 := this
      have : p ≃ q := (le_gt_false ‹ε ≤ ε/2› ‹ε > ε/2›).elim
      exact this
    | Or.inr (_ : dist p q ≃ 0) =>
      have : p ≃ q := dist_zero.mp ‹dist p q ≃ 0›
      exact this
  case mpr =>
    intro (_ : p ≃ q) (ε : ℚ) (_ : ε > 0)
    show p ⊢ε⊣ q
    have : dist p q ≤ ε := calc
      _ ≃ dist p q := eqv_refl
      _ ≃ 0        := dist_zero.mpr ‹p ≃ q›
      _ ≤ ε        := le_cases.mpr (Or.inl ‹ε > 0›)
    have : p ⊢ε⊣ q := close_dist.mpr ‹dist p q ≤ ε›
    exact this

/--
ε-closeness is symmetric.

**Property and proof intuition**: ε-closeness is a constraint on distance, and
distance is symmetric.
-/
theorem close_symm {ε p q : ℚ} : p ⊢ε⊣ q → q ⊢ε⊣ p := by
  intro (_ : p ⊢ε⊣ q)
  show q ⊢ε⊣ p
  have : dist p q ≤ ε := close_dist.mp ‹p ⊢ε⊣ q›
  have : dist q p ≤ ε := le_substL_eqv dist_comm this
  have : q ⊢ε⊣ p := close_dist.mpr this
  exact this

/--
ε-closeness obeys a form of transitivity, where the transitive distance is the
sum of the input distances.

**Property and proof intuition**: By the triangle inequality, we know that in
the worst case, the distance between the first and last values might be the sum
of the intermediate distances.
-/
theorem close_trans {ε δ p q r : ℚ} : p ⊢ε⊣ q → q ⊢δ⊣ r → p ⊢ε+δ⊣ r := by
  intro (_ : p ⊢ε⊣ q) (_ : q ⊢δ⊣ r)
  show p ⊢ε+δ⊣ r
  have : dist p q ≤ ε := close_dist.mp ‹p ⊢ε⊣ q›
  have : dist q r ≤ δ := close_dist.mp ‹q ⊢δ⊣ r›
  have : dist p r ≤ ε + δ := calc
    _ ≃ dist p r            := eqv_refl
    _ ≤ dist p q + dist q r := dist_triangle
    _ ≤ ε + dist q r        := le_substL_add ‹dist p q ≤ ε›
    _ ≤ ε + δ               := le_substR_add ‹dist q r ≤ δ›
  have : p ⊢ε+δ⊣ r := close_dist.mpr this
  exact this

/--
Substitution of an equivalent left argument to ε-closeness.

**Property intuition**: This must be true for any relation that's agnostic to
the implementation of rational numbers.

**Proof intuition**: Expand the distance definition of ε-closeness, then use
substitution.
-/
theorem close_substL_eqv {ε p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ ⊢ε⊣ q → p₂ ⊢ε⊣ q := by
  intro (_ : p₁ ≃ p₂) (_ : p₁ ⊢ε⊣ q)
  show p₂ ⊢ε⊣ q
  have : dist p₁ q ≤ ε := close_dist.mp ‹p₁ ⊢ε⊣ q›
  have : dist p₂ q ≤ ε := le_substL_eqv (dist_substL ‹p₁ ≃ p₂›) this
  have : p₂ ⊢ε⊣ q := close_dist.mpr this
  exact this

/--
Substitution of an equivalent middle argument to ε-closeness.

**Property intuition**: This must be true for any relation that's agnostic to
the implementation of rational numbers.

**Proof intuition**: Expand the distance definition of ε-closeness, then use
substitution.
-/
theorem close_substM_eqv {ε₁ ε₂ p q : ℚ} : ε₁ ≃ ε₂ → p ⊢ε₁⊣ q → p ⊢ε₂⊣ q := by
  intro (_ : ε₁ ≃ ε₂) (_ : p ⊢ε₁⊣ q)
  show p ⊢ε₂⊣ q
  have : dist p q ≤ ε₁ := close_dist.mp ‹p ⊢ε₁⊣ q›
  have : dist p q ≤ ε₂ := le_substR_eqv ‹ε₁ ≃ ε₂› this
  have : p ⊢ε₂⊣ q := close_dist.mpr this
  exact this

/--
Substitution of an equivalent right argument to ε-closeness.

**Property intuition**: This must be true for any relation that's agnostic to
the implementation of rational numbers.

**Proof intuition**: Swap the left and right arguments via symmetry, then use
the left-handed version of this property.
-/
theorem close_substR_eqv {ε p q₁ q₂ : ℚ} : q₁ ≃ q₂ → p ⊢ε⊣ q₁ → p ⊢ε⊣ q₂ := by
  intro (_ : q₁ ≃ q₂) (_ : p ⊢ε⊣ q₁)
  show p ⊢ε⊣ q₂
  have : q₁ ⊢ε⊣ p := close_symm ‹p ⊢ε⊣ q₁›
  have : q₂ ⊢ε⊣ p := close_substL_eqv ‹q₁ ≃ q₂› this
  have : p ⊢ε⊣ q₂ := close_symm this
  exact this

/--
Add a common right term to ε-closeness's outer arguments.

**Property intuition**: Translating two points by the same amount doesn't
change the distance between them.

**Proof intuition**: Expand ε-closeness into distance and delegate to its
properties.
-/
theorem close_substL_add {ε p q r : ℚ} : p ⊢ε⊣ q → p + r ⊢ε⊣ q + r := by
  intro (_ : p ⊢ε⊣ q)
  show p + r ⊢ε⊣ q + r
  have : dist p q ≤ ε := close_dist.mp ‹p ⊢ε⊣ q›
  have : dist (p + r) (q + r) ≤ ε := calc
    _ ≃ dist (p + r) (q + r) := eqv_refl
    _ ≃ dist p q             := dist_cancelR_add
    _ ≤ ε                    := ‹dist p q ≤ ε›
  have : p + r ⊢ε⊣ q + r := close_dist.mpr this
  exact this

/--
Add a common left term to ε-closeness's outer arguments.

**Property intuition**: Translating two points by the same amount doesn't
change the distance between them.

**Proof intuition**: Convert the left-handed version of this property using
commutativity of addition.
-/
theorem close_substR_add {ε p q r : ℚ} : p ⊢ε⊣ q → r + p ⊢ε⊣ r + q := by
  intro (_ : p ⊢ε⊣ q)
  show r + p ⊢ε⊣ r + q
  have : p + r ⊢ε⊣ q + r := close_substL_add ‹p ⊢ε⊣ q›
  have : r + p ⊢ε⊣ q + r := close_substL_eqv add_comm this
  have : r + p ⊢ε⊣ r + q := close_substR_eqv add_comm this
  exact this

/--
Negate ε-closeness's outer arguments.

**Property intuition**: Reflecting two points through zero doesn't change the
distance between them.

**Proof intuition**: Expand ε-closeness into distance and delegate to its
properties.
-/
theorem close_subst_neg {ε p q : ℚ} : p ⊢ε⊣ q → -p ⊢ε⊣ -q := by
  intro (_ : p ⊢ε⊣ q)
  show -p ⊢ε⊣ -q
  have : dist p q ≤ ε := close_dist.mp ‹p ⊢ε⊣ q›
  have : dist (-p) (-q) ≤ ε := le_substL_eqv (eqv_symm dist_cancel_neg) this
  have : -p ⊢ε⊣ -q := close_dist.mpr this
  exact this

/--
Subtract a common term from ε-closeness's outer arguments.

**Property intuition**: Translating two points by the same amount doesn't
change the distance between them.

**Proof intuition**: Add a negated right term to the outer arguments, then
convert into subtraction.
-/
theorem close_substL_sub {ε p q r : ℚ} : p ⊢ε⊣ q → p - r ⊢ε⊣ q - r := by
  intro (_ : p ⊢ε⊣ q)
  show p - r ⊢ε⊣ q - r
  have : p + (-r) ⊢ε⊣ q + (-r) := close_substL_add ‹p ⊢ε⊣ q›
  have : p - r ⊢ε⊣ q + (-r) := close_substL_eqv (eqv_symm sub_add_neg) this
  have : p - r ⊢ε⊣ q - r := close_substR_eqv (eqv_symm sub_add_neg) this
  exact this

/--
Subtract ε-closeness's outer arguments from a common term.

**Property intuition**: Translating two points by the same amount doesn't
change the distance between them.

**Proof intuition**: Negate the outer arguments, add a common left term, and
then convert into subtraction.
-/
theorem close_substR_sub {ε p q r : ℚ} : p ⊢ε⊣ q → r - p ⊢ε⊣ r - q := by
  intro (_ : p ⊢ε⊣ q)
  show r - p ⊢ε⊣ r - q
  have : -p ⊢ε⊣ -q := close_subst_neg ‹p ⊢ε⊣ q›
  have : r + (-p) ⊢ε⊣ r + (-q) := close_substR_add this
  have : r - p ⊢ε⊣ r + (-q) := close_substL_eqv (eqv_symm sub_add_neg) this
  have : r - p ⊢ε⊣ r - q := close_substR_eqv (eqv_symm sub_add_neg) this
  exact this

/--
Statements of ε-closeness can be added argument-by-argument.

**Intuition**: The ε in ε-closeness is preserved when adding the same value to
both endpoints (translation). By carefully picking which value to add to each
of the ε-closeness inputs, the right endpoint of the first can be made to match
the left endpoint of the second. Then the distances add by transitivity.
-/
theorem close_add_pointwise
    {ε δ p q r s : ℚ} : p ⊢ε⊣ q → r ⊢δ⊣ s → p + r ⊢ε+δ⊣ q + s
    := by
  intro (_ : p ⊢ε⊣ q) (_ : r ⊢δ⊣ s)
  show p + r ⊢ε+δ⊣ q + s
  have : p + r ⊢ε⊣ q + r := close_substL_add ‹p ⊢ε⊣ q›
  have : q + r ⊢δ⊣ q + s := close_substR_add ‹r ⊢δ⊣ s›
  have : p + r ⊢ε+δ⊣ q + s := close_trans ‹p + r ⊢ε⊣ q + r› ‹q + r ⊢δ⊣ q + s›
  exact this

/--
Statements of ε-closeness can be subtracted argument-by-argument.

**Intuition**: The ε in ε-closeness is preserved when subtracting the same
value from both endpoints, or subtracting both endpoints from the same value
(translation). By carefully picking the subtraction for each of the ε-closeness
inputs, the right endpoint of the first can be made to match the left endpoint
of the second. Then the distances add by transitivity.
-/
theorem close_sub_pointwise
    {ε δ p q r s : ℚ} : p ⊢ε⊣ q → r ⊢δ⊣ s → p - r ⊢ε+δ⊣ q - s
    := by
  intro (_ : p ⊢ε⊣ q) (_ : r ⊢δ⊣ s)
  show p - r ⊢ε+δ⊣ q - s
  have : p - r ⊢ε⊣ q - r := close_substL_sub ‹p ⊢ε⊣ q›
  have : q - r ⊢δ⊣ q - s := close_substR_sub ‹r ⊢δ⊣ s›
  have : p - r ⊢ε+δ⊣ q - s := close_trans ‹p - r ⊢ε⊣ q - r› ‹q - r ⊢δ⊣ q - s›
  exact this

/--
The ε in ε-closeness can always be replaced by a greater value.

**Property intuition**: ε-closeness represents a maximum distance, so a larger
maximum is trivial because it's less precise.

**Proof intuition**: Convert ε-closeness to a distance inequality; the result
follows by transitivity of order.
-/
theorem close_widen {ε ε' p q : ℚ} : p ⊢ε⊣ q → ε' > ε → p ⊢ε'⊣ q := by
  intro (_ : p ⊢ε⊣ q) (_ : ε' > ε)
  show p ⊢ε'⊣ q
  have : dist p q ≤ ε := close_dist.mp ‹p ⊢ε⊣ q›
  have : ε ≤ ε' := le_cases.mpr (Or.inl ‹ε < ε'›)
  have : dist p q ≤ ε' := le_trans ‹dist p q ≤ ε› ‹ε ≤ ε'›
  have : p ⊢ε'⊣ q := close_dist.mpr this
  exact this

/--
Convert ε-closeness to and from an "ordered betweenness" representation.

**Property intuition**: For two values to be ε-close, the second value must be
at most `ε` less than, or `ε` greater than, the first value.

**Proof intuition**: Convert ε-closeness to an upper bound on an absolute
value. That splits into a lower bound and an upper bound. Rewrite those bounds
using algebra to get the "ordered betweenness" form.
-/
theorem close_endpoints {ε p q : ℚ} : p ⊢ε⊣ q ↔ p-ε ≤ q ∧ q ≤ p+ε := calc
  _ ↔ p ⊢ε⊣ q            := Iff.rfl
  _ ↔ dist p q ≤ ε       := close_dist
  _ ↔ dist q p ≤ ε       := iff_subst_eqv le_substL_eqv (dist_comm (p := p))
  _ ↔ abs (q-p) ≤ ε      := iff_subst_eqv le_substL_eqv (dist_abs (p := q))
  _ ↔ -ε ≤ q-p ∧ q-p ≤ ε := abs_upper_bound
  _ ↔ p-ε ≤ q ∧ q-p ≤ ε  := iff_subst_covar and_mapL le_diff_lower
  _ ↔ p-ε ≤ q ∧ q ≤ p+ε  := iff_subst_covar and_mapR le_diff_upper

/--
Convert "ordered betweenness" to and from a "min-max" representation of "full"
betweenness.

This theorem holds the common logic for the ordered/min-max corollaries below.

**Property intuition**: The hypothesis that provides the ordering of the
exterior values is only needed for the reverse direction, to simplify `min` and
`max`. The forward direction is true just from the ordering implied by
"ordered betweenness".

**Proof intuition**: Use the hypothesis that orders the exterior values to
create equivalences for the `min` and `max` expressions. Then substitute those
equivalences on one side of the iff to produce the other.
-/
theorem order_iff_min_max
    {p q r : ℚ} : p ≤ q → (p ≤ r ∧ r ≤ q ↔ min p q ≤ r ∧ r ≤ max p q)
    := by
  intro (_ : p ≤ q)
  show p ≤ r ∧ r ≤ q ↔ min p q ≤ r ∧ r ≤ max p q
  have : p ≃ min p q := eqv_symm (min_le.mpr ‹p ≤ q›)
  have : q ≃ max p q := eqv_symm (max_le.mpr ‹p ≤ q›)
  have p_min : p ≤ r ↔ min p q ≤ r := iff_subst_eqv le_substL_eqv ‹p ≃ min p q›
  have q_max : r ≤ q ↔ r ≤ max p q := iff_subst_eqv le_substR_eqv ‹q ≃ max p q›
  calc
    _ ↔ p ≤ r ∧ r ≤ q             := Iff.rfl
    _ ↔ min p q ≤ r ∧ r ≤ q       := iff_subst_covar and_mapL p_min
    _ ↔ min p q ≤ r ∧ r ≤ max p q := iff_subst_covar and_mapR q_max

/--
Convert "ordered betweenness" to the "min-max" form of betweenness.

**Property and proof intuition**: Directly follows from `order_iff_min_max`;
the exterior values ordering hypothesis of that theorem can be derived from
"ordered betweenness".
-/
theorem min_max_from_order
    {p q r : ℚ} : p ≤ r ∧ r ≤ q → min p q ≤ r ∧ r ≤ max p q
    := by
  intro (order : p ≤ r ∧ r ≤ q)
  show min p q ≤ r ∧ r ≤ max p q
  have (And.intro (_ : p ≤ r) (_ : r ≤ q)) := order
  have : p ≤ q := le_trans ‹p ≤ r› ‹r ≤ q›
  have : min p q ≤ r ∧ r ≤ max p q := (order_iff_min_max this).mp order
  exact this

/--
Convert the "min-max" form of betweenness to "ordered betweenness", given an
ordering of the exterior values.

**Property and proof intuition**: Directly follows from `order_iff_min_max`.
-/
theorem order_from_min_max
    {p q r : ℚ} : min p q ≤ r ∧ r ≤ max p q → p ≤ q → p ≤ r ∧ r ≤ q
    := by
  intro (_ : min p q ≤ r ∧ r ≤ max p q) (_ : p ≤ q)
  show p ≤ r ∧ r ≤ q
  exact (order_iff_min_max ‹p ≤ q›).mpr ‹min p q ≤ r ∧ r ≤ max p q›

/--
A lemma that reverses the order of the operands in the "min-max" form of
betweenness.

**Property and proof intuition**: We already know that the `min` and `max`
functions are commutative; this is a trivial application of that property and
substitution.
-/
theorem min_max_comm
    {p q r : ℚ} : min p r ≤ q ∧ q ≤ max p r → min r p ≤ q ∧ q ≤ max r p
    := by
  intro (And.intro (_ : min p r ≤ q) (_ : q ≤ max p r))
  show min r p ≤ q ∧ q ≤ max r p
  have : min r p ≤ q := le_substL_eqv min_comm ‹min p r ≤ q›
  have : q ≤ max r p := le_substR_eqv max_comm ‹q ≤ max p r›
  exact And.intro ‹min r p ≤ q› ‹q ≤ max r p›

/--
Betweenness can be expressed as two inequalities involving the `min` and `max`
functions.

**Property intuition**: If a value `q` is between boundary values `p` and `r`,
that means it's greater than the smaller boundary value and less than the
larger boundary value.

**Proof intuition**: We use the "order" representation of betweenness, which
has two cases, one for each possible ordering of the boundary values. In the
forward direction, for each "order" case, replace the specific boundary values
with their minimum and maximum. In the reverse direction, start with the two
possible orderings of the boundary values, and in each case, convert the
minimum and maximum to the specific values for the corresponding "order" case.
-/
theorem between_min_max {p q r : ℚ} : p⊣ q ⊢r ↔ min p r ≤ q ∧ q ≤ max p r := by
  apply Iff.intro
  case mp =>
    intro (_ : p⊣ q ⊢r)
    show min p r ≤ q ∧ q ≤ max p r
    have : p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p := between_order.mp ‹p⊣ q ⊢r›
    match this with
    | Or.inl (_ : p ≤ q ∧ q ≤ r) =>
      have : min p r ≤ q ∧ q ≤ max p r := min_max_from_order ‹p ≤ q ∧ q ≤ r›
      exact this
    | Or.inr (_ : r ≤ q ∧ q ≤ p) =>
      have : min r p ≤ q ∧ q ≤ max r p := min_max_from_order ‹r ≤ q ∧ q ≤ p›
      have : min p r ≤ q ∧ q ≤ max p r := min_max_comm this
      exact this
  case mpr =>
    intro (min_max : min p r ≤ q ∧ q ≤ max p r)
    show p⊣ q ⊢r
    have : p ≤ r ∨ r ≤ p := le_dichotomy
    have : p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p :=
      match ‹p ≤ r ∨ r ≤ p› with
      | Or.inl (_ : p ≤ r) =>
        have : p ≤ q ∧ q ≤ r := order_from_min_max min_max ‹p ≤ r›
        Or.inl this
      | Or.inr (_ : r ≤ p) =>
        have : min r p ≤ q ∧ q ≤ max r p := min_max_comm min_max
        have : r ≤ q ∧ q ≤ p := order_from_min_max this ‹r ≤ p›
        Or.inr this
    have : p⊣ q ⊢r := between_order.mpr ‹p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p›
    exact this

/--
Convert ε-closeness into "lying between extremes".

**Property and proof intuition**: The values that are as far as possible from
`p`, while still being `ε`-close to it, are `p-ε` and `p+ε`; they are the only
two values that are exactly `ε` away from `p`. Thus any value `q` that is
`ε`-close to `p` must lie between those extremes.
-/
theorem between_from_close {ε p q : ℚ} : p ⊢ε⊣ q → p-ε⊣ q ⊢p+ε := by
  intro (_ : p ⊢ε⊣ q)
  show p-ε⊣ q ⊢p+ε
  have : p-ε ≤ q ∧ q ≤ p+ε := close_endpoints.mp ‹p ⊢ε⊣ q›
  have : (p-ε ≤ q ∧ q ≤ p+ε) ∨ (p+ε ≤ q ∧ q ≤ p-ε) := Or.inl this
  have : p-ε⊣ q ⊢p+ε := between_order.mpr this
  exact this

/--
Convert "lying between extremes" into ε-closeness.

**Property intuition**: The values that are as far as possible from `p`, while
still being `ε`-close to it, are `p-ε` and `p+ε`; they are the only two values
that are exactly `ε` away from `p`. Thus any value `q` that is `ε`-close to `p`
must lie between those extremes. We require a nonnegative `ε` for `ε`-closeness
to be meaningful.

**Proof intuition**: We can easily produce `ε`-closeness from betweeness if we
know which of `p-ε` and `p+ε` are greater. This can be deduced from `ε`'s
nonnegativity, which implies `-ε ≤ ε`.
-/
theorem close_from_between {ε p q : ℚ} : ε ≥ 0 → p-ε⊣ q ⊢p+ε → p ⊢ε⊣ q := by
  intro (_ : ε ≥ 0) (_ : p-ε⊣ q ⊢p+ε)
  show p ⊢ε⊣ q
  have : -ε ≤ ε := le_neg_nonneg ‹ε ≥ 0›
  have : p-ε ≤ p+ε := calc
    _ ≃ p - ε    := eqv_refl
    _ ≃ p + (-ε) := sub_add_neg
    _ ≤ p + ε    := le_substR_add ‹-ε ≤ ε›
  have : min (p-ε) (p+ε) ≤ q ∧ q ≤ max (p-ε) (p+ε) :=
    between_min_max.mp ‹p-ε⊣ q ⊢p+ε›
  have : p-ε ≤ q ∧ q ≤ p+ε := order_from_min_max this ‹p-ε ≤ p+ε›
  have : p ⊢ε⊣ q := close_endpoints.mpr this
  exact this

/--
A transitivity-like property of betweenness.

**Property intuition**: Call `p` and `t` "outer values", and `q` and `s`
"middle values", because the latter are between the former. We also have an
"inner value" `r` that sits between the middle values. Then `r` must also be
between the outer values.

**Proof intuition**: Both the outer values and the middle values have one value
smaller† than the other. The smaller outer value is less than the smaller
middle value, which is less than the inner value. By transitivity of order, the
smaller outer value is less than the inner value. A similar argument for the
larger values implies that the inner value is less than the larger outer value.
Thus the inner value is between the outer values.

†Or equivalent to, but it's easier to explain the general solution using strict
order.
-/
theorem between_trans
    {p q r s t : ℚ} : p⊣ q ⊢t → p⊣ s ⊢t → q⊣ r ⊢s → p⊣ r ⊢t
    := by
  intro (_ : p⊣ q ⊢t) (_ : p⊣ s ⊢t) (_ : q⊣ r ⊢s)
  show p⊣ r ⊢t
  have (And.intro (_ : min p t ≤ q) (_ : q ≤ max p t)) :=
    between_min_max.mp ‹p⊣ q ⊢t›
  have (And.intro (_ : min p t ≤ s) (_ : s ≤ max p t)) :=
    between_min_max.mp ‹p⊣ s ⊢t›
  have (And.intro (_ : min q s ≤ r) (_ : r ≤ max q s)) :=
    between_min_max.mp ‹q⊣ r ⊢s›
  have : min p t ≤ min q s := min_le_both ‹min p t ≤ q› ‹min p t ≤ s›
  have : max q s ≤ max p t := max_le_both ‹q ≤ max p t› ‹s ≤ max p t›
  have : min p t ≤ r := le_trans ‹min p t ≤ min q s› ‹min q s ≤ r›
  have : r ≤ max p t := le_trans ‹r ≤ max q s› ‹max q s ≤ max p t›
  have : min p t ≤ r ∧ r ≤ max p t := And.intro ‹min p t ≤ r› ‹r ≤ max p t›
  have : p⊣ r ⊢t := between_min_max.mpr this
  exact this

/--
Derive an ε-closeness property for a value between two others.

**Property intuition**: Any value between `q` and `s` would have to be
`ε`-close to `p`, since `q` and `s` themselves are; if there were some values
between that weren't `ε`-close to `p`, then at least one of `q` and `s` would
not be `ε`-close to `p` anymore.

**Proof intuition**: Reframe the `ε`-closeness of `q` and `s` to `p` as each of
them being between `p-ε` and `p+ε`. Then `r` must also be between `p-ε` and
`p+ε`, because it's between `q` and `s`. Therefore `r` is `ε`-close to `p`.
-/
theorem between_preserves_close
    {ε p q r s : ℚ} : p ⊢ε⊣ q → p ⊢ε⊣ s → q⊣ r ⊢s → p ⊢ε⊣ r
    := by
  intro (_ : p ⊢ε⊣ q) (_ : p ⊢ε⊣ s) (_ : q⊣ r ⊢s)
  show p ⊢ε⊣ r
  have : ε ≥ 0 := close_nonneg ‹p ⊢ε⊣ q›
  have : p-ε⊣ q ⊢p+ε := between_from_close ‹p ⊢ε⊣ q›
  have : p-ε⊣ s ⊢p+ε := between_from_close ‹p ⊢ε⊣ s›
  have : p-ε⊣ r ⊢p+ε := between_trans ‹p-ε⊣ q ⊢p+ε› ‹p-ε⊣ s ⊢p+ε› ‹q⊣ r ⊢s›
  have : p ⊢ε⊣ r := close_from_between ‹ε ≥ 0› ‹p-ε⊣ r ⊢p+ε›
  exact this

/--
Scale ε-close values by a factor on the right.

**Property intuition**: Multiplication "expands" or "contracts" distance, so
we'd expect the scaling factor to be accounted for in the ε part of the
ε-closeness relation.

**Proof intuition**: Expand ε-closeness into an upper bound on distance, then
use the distributive property of distance and the fact that multiplication by a
nonnegative value preserves order.
-/
theorem close_substL_mul
    {ε p q r : ℚ} : p ⊢ε⊣ q → p * r ⊢ε * abs r⊣ q * r
    := by
  intro (_ : p ⊢ε⊣ q)
  show p * r ⊢ε * abs r⊣ q * r
  have : dist p q ≤ ε := close_dist.mp ‹p ⊢ε⊣ q›
  have : abs r ≥ 0 := abs_nonneg
  have : dist (p * r) (q * r) ≤ ε * abs r := calc
    _ ≃ dist (p * r) (q * r) := eqv_refl
    _ ≃ dist p q * abs r     := eqv_symm dist_distribR
    _ ≤ ε * abs r            := le_substL_mul_nonneg this ‹dist p q ≤ ε›
  have : p * r ⊢ε * abs r⊣ q * r := close_dist.mpr this
  exact this

/--
Scale ε-close values by a factor on the left.

**Property intuition**: Multiplication "expands" or "contracts" distance, so
we'd expect the scaling factor to be accounted for in the ε part of the
ε-closeness relation.

**Proof intuition**: This is equivalent to the opposite-handed theorem, but
with all multiplications flipped around by commutativity.
-/
theorem close_substR_mul
    {ε p q r : ℚ} : p ⊢ε⊣ q → r * p ⊢(abs r) * ε⊣ r * q
    := by
  intro (_ : p ⊢ε⊣ q)
  show r * p ⊢(abs r) * ε⊣ r * q
  have : p * r ⊢ε * abs r⊣ q * r := close_substL_mul ‹p ⊢ε⊣ q›
  have : r * p ⊢ε * abs r⊣ q * r := close_substL_eqv mul_comm this
  have : r * p ⊢(abs r) * ε⊣ q * r := close_substM_eqv mul_comm this
  have : r * p ⊢(abs r) * ε⊣ r * q := close_substR_eqv mul_comm this
  exact this

/--
Multiply corresponding values of two ε-closeness relations.

**Property and proof intuition**: The relation `p ⊢ε⊣ q` can be viewed as
roughly saying that `q ≃ p + ε`. Thus `r ⊢δ⊣ s` means `s ≃ r + δ`. Multiplying,
we obtain `qs ≃ (p + ε)(r + δ) ≃ pr + (εr + δp + εδ)`, implying the goal.
-/
theorem close_mul_pointwise
    {ε δ p q r s : ℚ}
    : p ⊢ε⊣ q → r ⊢δ⊣ s → p * r ⊢ε * abs r + δ * abs p + ε * δ⊣ q * s
    := by
  intro (_ : p ⊢ε⊣ q) (_ : r ⊢δ⊣ s)
  show p * r ⊢ε * abs r + δ * abs p + ε * δ⊣ q * s

  have close_diff
      {x y ζ : ℚ} : x ⊢ζ⊣ y → ∃ (d : ℚ), y ≃ x + d ∧ abs d ≤ ζ
      := by
    intro (_ : x ⊢ζ⊣ y)
    show ∃ (d : ℚ), y ≃ x + d ∧ abs d ≤ ζ
    let d := y - x
    have : y ≃ x + d := calc
      _ ≃ y            := eqv_refl
      _ ≃ y + 0        := eqv_symm add_identR
      _ ≃ y + (-x + x) := add_substR (eqv_symm add_inverseL)
      _ ≃ (y + -x) + x := eqv_symm add_assoc
      _ ≃ (y - x) + x  := add_substL (eqv_symm sub_add_neg)
      _ ≃ d + x        := add_substL eqv_refl
      _ ≃ x + d        := add_comm
    have : abs d ≤ ζ := calc
      _ ≃ abs d       := eqv_refl
      _ ≃ abs (y - x) := eqv_refl
      _ ≃ dist y x    := eqv_symm dist_abs
      _ ≃ dist x y    := dist_comm
      _ ≤ ζ           := close_dist.mp ‹x ⊢ζ⊣ y›
    exact Exists.intro d (And.intro ‹y ≃ x + d› ‹abs d ≤ ζ›)

  have (Exists.intro (a : ℚ) (And.intro (_ : q ≃ p + a) (_ : abs a ≤ ε))) :=
    close_diff ‹p ⊢ε⊣ q›
  have (Exists.intro (b : ℚ) (And.intro (_ : s ≃ r + b) (_ : abs b ≤ δ))) :=
    close_diff ‹r ⊢δ⊣ s›

  have : ε ≥ 0 := close_nonneg ‹p ⊢ε⊣ q›
  have : s - r ≃ b := calc
    _ ≃ s - r        := eqv_refl
    _ ≃ s + -r       := sub_add_neg
    _ ≃ -r + s       := add_comm
    _ ≃ -r + (r + b) := add_substR ‹s ≃ r + b›
    _ ≃ (-r + r) + b := eqv_symm add_assoc
    _ ≃ 0 + b        := add_substL add_inverseL
    _ ≃ b            := add_identL
  have qs_pr_eqv_pb_ar_ab : q * s - p * r ≃ p * b + a * r + a * b := calc
    _ ≃ q * s - p * r                := eqv_refl
    _ ≃ (p + a) * s - p * r          := sub_substL (mul_substL ‹q ≃ p + a›)
    _ ≃ p * s + a * s - p * r        := sub_substL mul_distribR
    _ ≃ p * s + a * s + (-(p * r))   := sub_add_neg
    _ ≃ p * s + (a * s + (-(p * r))) := add_assoc
    _ ≃ p * s + (-(p * r) + a * s)   := add_substR add_comm
    _ ≃ p * s + (-(p * r)) + a * s   := eqv_symm add_assoc
    _ ≃ p * s - p * r + a * s        := add_substL (eqv_symm sub_add_neg)
    _ ≃ p * (s - r) + a * s          := add_substL (eqv_symm mul_distribL_sub)
    _ ≃ p * b + a * s                := add_substL (mul_substR ‹s - r ≃ b›)
    _ ≃ p * b + a * (r + b)          := add_substR (mul_substR ‹s ≃ r + b›)
    _ ≃ p * b + (a * r + a * b)      := add_substR mul_distribL
    _ ≃ p * b + a * r + a * b        := eqv_symm add_assoc
  have : abs (a * r) ≤ ε * abs r := calc
    _ ≃ abs (a * r)   := eqv_refl
    _ ≃ abs a * abs r := abs_compat_mul
    _ ≤ ε * abs r     := le_substL_mul_nonneg abs_nonneg ‹abs a ≤ ε›
  have : abs (p * b) ≤ δ * abs p := calc
    _ ≃ abs (p * b)   := eqv_refl
    _ ≃ abs p * abs b := abs_compat_mul
    _ ≤ abs p * δ     := le_substR_mul_nonneg abs_nonneg ‹abs b ≤ δ›
    _ ≃ δ * abs p     := mul_comm
  have abs_ab : abs (a * b) ≤ ε * δ := calc
    _ ≃ abs (a * b)   := eqv_refl
    _ ≃ abs a * abs b := abs_compat_mul
    _ ≤ ε * abs b     := le_substL_mul_nonneg abs_nonneg ‹abs a ≤ ε›
    _ ≤ ε * δ         := le_substR_mul_nonneg ‹ε ≥ 0› ‹abs b ≤ δ›
  have abs_pb_ar : abs (p * b + a * r) ≤ ε * abs r + δ * abs p := calc
    _ ≃ abs (p * b + a * r)       := eqv_refl
    _ ≤ abs (p * b) + abs (a * r) := abs_compat_add
    _ ≤ δ * abs p + abs (a * r)   := le_substL_add ‹abs (p * b) ≤ δ * abs p›
    _ ≤ δ * abs p + ε * abs r     := le_substR_add ‹abs (a * r) ≤ ε * abs r›
    _ ≃ ε * abs r + δ * abs p     := add_comm
  have : dist (p * r) (q * s) ≤ ε * abs r + δ * abs p + ε * δ := calc
    _ ≃ dist (p * r) (q * s)                := eqv_refl
    _ ≃ dist (q * s) (p * r)                := dist_comm
    _ ≃ abs (q * s - p * r)                 := dist_abs
    _ ≃ abs (p * b + a * r + a * b)         := abs_subst qs_pr_eqv_pb_ar_ab
    _ ≤ abs (p * b + a * r) + abs (a * b)   := abs_compat_add
    _ ≤ ε * abs r + δ * abs p + abs (a * b) := le_substL_add abs_pb_ar
    _ ≤ ε * abs r + δ * abs p + ε * δ       := le_substR_add abs_ab
  have : p * r ⊢ε * abs r + δ * abs p + ε * δ⊣ q * s := close_dist.mpr this
  exact this

end Lean4Axiomatic.Rational
