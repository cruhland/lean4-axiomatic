import Lean4Axiomatic.Rational.Multiplication

/-! # Rational numbers: negation and subtraction -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

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

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type}
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Subtraction ℚ]

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
Negating a subtraction operation swaps its operands.

For intuition, see the identical proof for integers, `Integer.sub_neg_flip`.
-/
theorem neg_sub {p q : ℚ} : -(p - q) ≃ q - p := calc
  -(p - q)             ≃ _ := eqv_symm mul_neg_one
  (-1) * (p - q)       ≃ _ := mul_substR sub_add_neg
  (-1) * (p + -q)      ≃ _ := mul_distribL
  (-1) * p + (-1) * -q ≃ _ := add_substL mul_neg_one
  (-p) + (-1) * -q     ≃ _ := add_substR mul_neg_one
  (-p) + -(-q)         ≃ _ := add_substR neg_involutive
  (-p) + q             ≃ _ := add_comm
  q + -p               ≃ _ := eqv_symm sub_add_neg
  q - p                ≃ _ := eqv_refl

/--
Two rational numbers are equal if and only if their difference is zero.

See `Integer.zero_diff_iff_eqv` for intuition.
-/
theorem sub_eqv_zero_iff_eqv {p q : ℚ} : p - q ≃ 0 ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p - q ≃ 0)
    show p ≃ q
    calc
      p            ≃ _ := eqv_symm add_identR
      p + 0        ≃ _ := add_substR (eqv_symm add_inverseL)
      p + (-q + q) ≃ _ := eqv_symm add_assoc
      (p + -q) + q ≃ _ := add_substL (eqv_symm sub_add_neg)
      (p - q) + q  ≃ _ := add_substL ‹p - q ≃ 0›
      0 + q        ≃ _ := add_identL
      q            ≃ _ := eqv_refl
  case mpr =>
    intro (_ : p ≃ q)
    show p - q ≃ 0
    calc
      p - q  ≃ _ := sub_add_neg
      p + -q ≃ _ := add_substL ‹p ≃ q›
      q + -q ≃ _ := add_inverseR
      0      ≃ _ := eqv_refl

end Lean4Axiomatic.Rational
