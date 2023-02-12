import Lean4Axiomatic.Logic
import Lean4Axiomatic.Rational.Multiplication

/-! # Rational numbers: inverse operations -/

namespace Lean4Axiomatic.Rational

open Logic (AP)
open Signed (Negative Positive)

/-! ## Axioms -/

/-- Operations pertaining to rational number negation. -/
class Negation.Ops (ℚ : Type) :=
  /-- Negation of rational numbers. -/
  neg : ℚ → ℚ

export Negation.Ops (neg)

/-- Enables the use of the `-·` operator for negation. -/
instance neg_op_inst {ℚ : Type} [Negation.Ops ℚ] : Neg ℚ := {
  neg := neg
}

/-- Properties of rational number negation. -/
class Negation.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Ops ℚ]
    :=
  /-- Negation respects equivalence over its operand. -/
  neg_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → -p₁ ≃ -p₂

  /-- Negation is consistent with its integer equivalent. -/
  neg_compat_from_integer {a : ℤ} : ((-a : ℤ) : ℚ) ≃ -(a : ℚ)

  /-- The negation of a value is its left additive inverse. -/
  add_inverseL {p : ℚ} : -p + p ≃ 0

  /-- The negation of a value is its right additive inverse. -/
  add_inverseR {p : ℚ} : p + -p ≃ 0

export Negation.Props (
  add_inverseL add_inverseR neg_compat_from_integer neg_subst
)

/-- All rational number negation axioms. -/
class Negation
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ]
    :=
  toOps : Negation.Ops ℚ
  toProps : Negation.Props ℚ

attribute [instance] Negation.toOps
attribute [instance] Negation.toProps

/-- Operations pertaining to rational number subtraction. -/
class Subtraction.Ops (ℚ : Type) :=
  /-- Subtraction of rational numbers. -/
  sub : ℚ → ℚ → ℚ

export Subtraction.Ops (sub)

/-- Enables the use of the `· - ·` operator for subtraction. -/
instance sub_op_inst {ℚ : Type} [Subtraction.Ops ℚ] : Sub ℚ := {
  sub := sub
}

/-- Properties of rational number subtraction. -/
class Subtraction.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ] [Ops ℚ]
    :=
  /-- Subtraction is equivalent to addition of a negated second argument. -/
  sub_add_neg {p q : ℚ} : p - q ≃ p + (-q)

export Subtraction.Props (sub_add_neg)

/-- All rational number subtraction axioms. -/
class Subtraction
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Negation ℚ]
    :=
  toOps : Subtraction.Ops ℚ
  toProps : Subtraction.Props ℚ

attribute [instance] Subtraction.toOps
attribute [instance] Subtraction.toProps

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
  recip_inverseL {p : ℚ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1

  /-- The reciprocal of a value is its right multiplicative inverse. -/
  recip_inverseR {p : ℚ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1

export Reciprocation.Props (recip_inverseL recip_inverseR recip_subst)

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

/-- All rational number inverse operation axioms. -/
class Inverse
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    :=
  toNegation : Negation ℚ
  toSubtraction : Subtraction ℚ
  toReciprocation : Reciprocation ℚ
  toDivision : Division ℚ

attribute [instance] Inverse.toDivision
attribute [instance] Inverse.toNegation
attribute [instance] Inverse.toReciprocation
attribute [instance] Inverse.toSubtraction

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type}
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Inverse ℚ]

/--
Zero is a left absorbing element for multiplication.

The proof is identical to `Integer.mul_absorbL`; see its comment for intuition.
-/
theorem mul_absorbL {p : ℚ} : 0 * p ≃ 0 := calc
  0 * p                      ≃ _ := eqv_symm add_identR
  0 * p + 0                  ≃ _ := add_substR (eqv_symm add_inverseR)
  0 * p + (0 * p + -(0 * p)) ≃ _ := eqv_symm add_assoc
  (0 * p + 0 * p) + -(0 * p) ≃ _ := add_substL (eqv_symm mul_distribR)
  (0 + 0) * p + -(0 * p)     ≃ _ := add_substL (mul_substL add_identL)
  0 * p + -(0 * p)           ≃ _ := add_inverseR
  0                          ≃ _ := eqv_refl

/--
Zero is a right absorbing element for multiplication.

This follows from left absorption because multiplication is commutative.
-/
theorem mul_absorbR {p : ℚ} : p * 0 ≃ 0 := calc
  p * 0 ≃ _ := mul_comm
  0 * p ≃ _ := mul_absorbL
  0     ≃ _ := eqv_refl

/--
The negation of a nonzero rational is also nonzero.

**Property intuition**: Negation produces the "mirror image" of a rational
number, reflected across zero. Any nonzero number will be some finite distance
away from zero, and so will its negation.

**Proof intuition**: Show that `-p ≃ 0` implies `p ≃ 0`, and take the
contrapositive.
-/
theorem neg_preserves_nonzero {p : ℚ} : p ≄ 0 → -p ≄ 0 := by
  intro (_ : p ≄ 0) (_ : -p ≃ 0)
  show False
  have : p ≃ 0 := calc
    p      ≃ _ := eqv_symm add_identR
    p + 0  ≃ _ := add_substR (eqv_symm ‹-p ≃ 0›)
    p + -p ≃ _ := add_inverseR
    0      ≃ _ := eqv_refl
  exact absurd ‹p ≃ 0› ‹p ≄ 0›

/-- Useful for having negated expressions under the division sign. -/
instance neg_preserves_nonzero_inst {p : ℚ} [AP (p ≄ 0)] : AP (-p ≄ 0) :=
  AP.mk (neg_preserves_nonzero ‹AP (p ≄ 0)›.ev)

/--
Negation is left-semicompatible with multiplication.

The proof is identical to `Integer.neg_scompatL_mul`; see its comment for
intuition.
-/
theorem neg_scompatL_mul {p q : ℚ} : -(p * q) ≃ -p * q := by
  have : 0 ≃ -p + p := eqv_symm add_inverseL
  calc
    -(p * q)                      ≃ _ := eqv_symm add_identL
    0 + -(p * q)                  ≃ _ := add_substL (eqv_symm mul_absorbL)
    0 * q + -(p * q)              ≃ _ := add_substL (mul_substL ‹0 ≃ -p + p›)
    (-p + p) * q + -(p * q)       ≃ _ := add_substL mul_distribR
    (-p * q + p * q) + -(p * q)   ≃ _ := add_assoc
    (-p) * q + (p * q + -(p * q)) ≃ _ := add_substR add_inverseR
    (-p) * q + 0                  ≃ _ := add_identR
    (-p) * q                      ≃ _ := eqv_refl

/--
Negation is right-semicompatible with multiplication.

This follows from left-semicompatibility because multiplication is commutative.
-/
theorem neg_scompatR_mul {p q : ℚ} : -(p * q) ≃ p * -q := calc
  (-(p * q)) ≃ _ := neg_subst mul_comm
  (-(q * p)) ≃ _ := neg_scompatL_mul
  (-q) * p   ≃ _ := mul_comm
  p * -q     ≃ _ := eqv_refl

/--
Multiplication by negative one is the same as negation.

The proof is identical to `Integer.mul_neg_one`; see its comment for intuition.
-/
theorem mul_neg_one {p : ℚ} : -1 * p ≃ -p := calc
  -1 * p     ≃ _ := eqv_symm neg_scompatL_mul
  (-(1 * p)) ≃ _ := neg_subst mul_identL
  (-p)       ≃ _ := eqv_refl

/--
Negating twice is the same as not negating at all.

The proof is identical to `Integer.neg_involutive`; see its comment for
intuition.
-/
theorem neg_involutive {p : ℚ} : -(-p) ≃ p := calc
  -(-p)            ≃ _ := eqv_symm add_identL
  0 + -(-p)        ≃ _ := add_substL (eqv_symm add_inverseR)
  (p + -p) + -(-p) ≃ _ := add_assoc
  p + (-p + -(-p)) ≃ _ := add_substR add_inverseR
  p + 0            ≃ _ := add_identR
  p                ≃ _ := eqv_refl

/--
The rational number `-1` is a square root of unity.

**Property and proof intuition**: This is a (nearly) trivial corollary of the
proof that integer square roots of unity are also rational square roots of
unity. There's a single, technical, complication in that the most natural
syntax for representing `-1` as a rational number is `(-1 : ℚ)`, but this is
interpreted as `(-(1 : ℤ) : ℚ)` by Lean, instead of the more convenient
`((-1 : ℤ) : ℚ)`.
-/
instance sqrt1_neg_one : Sqrt1 (-1 : ℚ) := by
  have : Integer.Sqrt1 (-1 : ℤ) := Integer.sqrt1_neg_one
  have : Sqrt1 ((-1 : ℤ) : ℚ) := from_integer_preserves_sqrt1.mpr this
  have : Sqrt1 (-1 : ℚ) := sqrt1_subst neg_compat_from_integer this
  exact this

/--
Square roots of unity are nonzero.

**Property and proof intuition**: Trivial because `p * p ≃ 1` can only hold if
`p ≄ 0`, otherwise the absorption property of zero would make the product zero.
-/
theorem sqrt1_nonzero {p : ℚ} : Sqrt1 p → p ≄ 0 := by
  intro (_ : Sqrt1 p) (_ : p ≃ 0)
  show False
  have : (1 : ℚ) ≃ 0 := calc
    (1 : ℚ) ≃ _ := eqv_symm ‹Sqrt1 p›.elim
    p * p   ≃ _ := mul_substL ‹p ≃ 0›
    0 * p   ≃ _ := mul_absorbL
    0       ≃ _ := eqv_refl
  have : (1 : ℚ) ≄ 0 := nonzero_one
  exact absurd ‹(1 : ℚ) ≃ 0› ‹(1 : ℚ) ≄ 0›

/--
Instance version of `sqrt1_nonzero`, to enable clean syntax for square roots of
unity in contexts where they need to be nonzero, such as taking reciprocals.
-/
instance sqrt1_nonzero_inst {p : ℚ} [Sqrt1 p] : AP (p ≄ 0) :=
  AP.mk (sqrt1_nonzero ‹Sqrt1 p›)

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
  s * (s * s⁻¹) ≃ _ := mul_substR recip_inverseR
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
