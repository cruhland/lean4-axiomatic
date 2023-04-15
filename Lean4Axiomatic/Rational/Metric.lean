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
The absolute value of a rational number is greater than or equivalent to zero.

**Property intuition**: The absolute value discards the sign of a number and
returns the magnitude, so we'd expect it to be nonnegative.

**Proof intuition**: The sign of a rational number's absolute value is that
number's sign squared. A square can never be negative, thus the absolute value
must be positive or zero.
-/
theorem abs_ge_zero {p : ℚ} : abs p ≥ 0 := by
  have : sgn (p * p) ≃ sgn (abs p) := calc
    sgn (p * p)     ≃ _ := sgn_compat_mul
    sgn p * sgn p   ≃ _ := Rel.symm sgn_abs
    sgn (abs p)     ≃ _ := Rel.refl
  have : sgn (abs p) ≄ -1 := AA.neqv_substL this nonneg_square
  have : abs p ≥ 0 := ge_zero_sgn.mpr this
  exact this

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
  abs (p + q)                       ≃ _ := abs_sgn
  (p + q) * sgn (p + q)             ≃ _ := mul_distribR
  p * sgn (p + q) + q * sgn (p + q) ≤ _ := add_substL_le mul_sgn_self_max
  p * sgn p + q * sgn (p + q)       ≤ _ := add_substR_le mul_sgn_self_max
  p * sgn p + q * sgn q             ≃ _ := add_substL (eqv_symm abs_sgn)
  abs p + q * sgn q                 ≃ _ := add_substR (eqv_symm abs_sgn)
  abs p + abs q                     ≃ _ := eqv_refl

end Lean4Axiomatic.Rational
