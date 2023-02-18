import Lean4Axiomatic.Rational.Negation

/-! # Rational numbers: reciprocation and division -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

/-- Operations pertaining to rational number reciprocation. -/
class Reciprocation.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    :=
  /-- Reciprocation of rational numbers. -/
  reciprocal (p : ℚ) [AP (p ≄ 0)] : ℚ

export Reciprocation.Ops (reciprocal)

/-- Enables the use of the `·⁻¹` operator for reciprocation. -/
postfix:120 "⁻¹" => reciprocal

/-- Properties of rational number reciprocation. -/
class Reciprocation.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Ops ℚ]
    :=
  /-- Reciprocation respects equivalence over its operand. -/
  recip_subst {p₁ p₂ : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹

  /-- The reciprocal of a value is its left multiplicative inverse. -/
  mul_inverseL {p : ℚ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1

  /-- The reciprocal of a value is its right multiplicative inverse. -/
  mul_inverseR {p : ℚ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1

export Reciprocation.Props (mul_inverseL mul_inverseR recip_subst)

/-- All rational number reciprocation axioms. -/
class Reciprocation
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    :=
  toOps : Reciprocation.Ops ℚ
  toProps : Reciprocation.Props ℚ

attribute [instance] Reciprocation.toOps
attribute [instance] Reciprocation.toProps

/-- Operations pertaining to rational number division. -/
class Division.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    :=
  /-- Division of rational numbers. -/
  div (p q : ℚ) [AP (q ≄ 0)] : ℚ

export Division.Ops (div)

/--
Enables the use of the `· / ·` operator for division.

We define the operator syntax directly here, instead of using the `Div` class
from the standard library. This is because our `div` operation has an extra
argument, an instance expressing that the divisor must be nonzero. The `Div`
class only provides a simple binary operation for its `div`.
-/
infixl:70 " / " => div

/--
An inductive predicate expressing that a rational number can be represented as
a ratio of integers.

A value of `AsRatio p`, for some rational number `p`, is an existence proof
that there are two integers `a` and `b` whose ratio `a / b` is equivalent to
`p`.
-/
inductive AsRatio
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Division.Ops ℚ] (p : ℚ)
    : Prop
    :=
  /-- Construct a value of `AsRatio p`. -/
| intro
    (a b : ℤ)
    (b_nonzero : Integer.Nonzero b)
    (eqv_ratio : p ≃ a / b)

/-- Properties of rational number division. -/
class Division.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]
      [Ops ℚ]
    :=
  /--
  Division is equivalent to multiplication by the reciprocal of the second
  argument.
  -/
  div_mul_recip {p q : ℚ} [AP (q ≄ 0)] : p / q ≃ p * q⁻¹

  /--
  Every rational number can be expressed as a ratio of integers.

  Given any two integers, we can easily make a rational number; convert both of
  them to rationals using `from_integer`, then divide them. This axiom tells us
  that we can also do the reverse: given any rational, there are two integers
  that produce it when put into a ratio.

  It's a useful axiom because it provides a way to "deconstruct" a rational
  number into simpler pieces, which may be easier to work with. Although it's
  preferable to work with rational numbers directly, and use this only when
  necessary.
  -/
  as_ratio (p : ℚ) : AsRatio p

export Division.Props (as_ratio div_mul_recip)

/-- All rational number division axioms. -/
class Division
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]
    :=
  toOps : Division.Ops ℚ
  toProps : Division.Props ℚ

attribute [instance] Division.toOps
attribute [instance] Division.toProps

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type}
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Reciprocation ℚ] [Division ℚ]

/--
Square roots of unity are their own reciprocals.

**Property intuition**: Taking the reciprocal of a number doesn't change its
sign, and the only fraction that would be unchanged when flipping it is `1/1`,
i.e. the rational number `1`. Thus `1` and `-1` should be the only numbers to
satisfy this property.

**Proof intuition**: The defining proprty of square roots of unity,
`s * s ≃ 1`, is cruical for this proof because it introduces two factors of
`s`. One of them gets canceled by the reciprocal, leaving the other as the
result.
-/
theorem recip_sqrt1 {s : ℚ} [Sqrt1 s] : s⁻¹ ≃ s := calc
  s⁻¹           ≃ _ := eqv_symm mul_identL
  1 * s⁻¹       ≃ _ := mul_substL (eqv_symm ‹Sqrt1 s›.elim)
  (s * s) * s⁻¹ ≃ _ := mul_assoc
  s * (s * s⁻¹) ≃ _ := mul_substR mul_inverseR
  s * 1         ≃ _ := mul_identR
  s             ≃ _ := eqv_refl

/--
Division respects equivalence over its left operand.

**Property intuition**: Necessary for division to be a valid function on
rational numbers.

**Proof intuition**: The left operand of division is also the left operand of
the underlying multiplication, which is already known to obey the substitution
property.
-/
theorem div_substL {p₁ p₂ q : ℚ} [AP (q ≄ 0)] : p₁ ≃ p₂ → p₁ / q ≃ p₂ / q := by
  intro (_ : p₁ ≃ p₂)
  show p₁ / q ≃ p₂ / q
  calc
    p₁ / q   ≃ _ := div_mul_recip
    p₁ * q⁻¹ ≃ _ := mul_substL ‹p₁ ≃ p₂›
    p₂ * q⁻¹ ≃ _ := eqv_symm div_mul_recip
    p₂ / q   ≃ _ := eqv_refl

/--
Division respects equivalence over its right operand.

**Property intuition**: Necessary for division to be a valid function on
rational numbers.

**Proof intuition**: Division's right operand's reciprocal is the underlying
multiplication's right operand. Multiplication and reciprocation are already
known to obey the substitution property.
-/
theorem div_substR
    {p₁ p₂ q : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → q / p₁ ≃ q / p₂
    := by
  intro (_ : p₁ ≃ p₂)
  show q / p₁ ≃ q / p₂
  calc
    q / p₁   ≃ _ := div_mul_recip
    q * p₁⁻¹ ≃ _ := mul_substR (recip_subst ‹p₁ ≃ p₂›)
    q * p₂⁻¹ ≃ _ := eqv_symm div_mul_recip
    q / p₂   ≃ _ := eqv_refl

end Lean4Axiomatic.Rational
