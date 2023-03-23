import Lean4Axiomatic.Rational.Sign

/-! # Rational numbers: order -/

namespace Lean4Axiomatic.Rational

open Signed (sgn)

/-! ## Axioms -/

/-- Operations pertaining to rational number order. -/
class Order.Ops (ℚ : Type) :=
  /-- Less than or equivalent to. -/
  le : ℚ → ℚ → Prop

  /-- Less than. -/
  lt : ℚ → ℚ → Prop

export Order.Ops (le lt)

/-- Enables the use of the `· ≤ ·` and `· ≥ ·` operators. -/
instance le_inst {ℚ : Type} [Order.Ops ℚ] : LE ℚ := {
  le := Order.Ops.le
}

/-- Enables the use of the `· < ·` and `· > ·` operators. -/
instance lt_inst {ℚ : Type} [Order.Ops ℚ] : LT ℚ := {
  lt := Order.Ops.lt
}

/-- Properties of rational number order. -/
class Order.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ] [Ops ℚ]
    :=
  /--
  A rational number is less than or equivalent to another when subtracting the
  latter from the former gives a non-positive result, i.e. its sign is not one.
  -/
  le_sgn {p q : ℚ} : p ≤ q ↔ sgn (p - q) ≄ 1

  /--
  A rational number is less than another when subtracting the latter from the
  former gives a negative result, i.e. its sign is negative one.
  -/
  lt_sgn {p q : ℚ} : p < q ↔ sgn (p - q) ≃ -1

export Order.Props (le_sgn lt_sgn)

/-- All rational number order axioms. -/
class Order
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
      [Negation ℚ] [Sign ℚ] [Subtraction ℚ]
    :=
  toOps : Order.Ops ℚ
  toProps : Order.Props ℚ

attribute [instance] Order.toOps
attribute [instance] Order.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
  [Sign ℚ] [Subtraction ℚ] [Reciprocation ℚ] [Division ℚ] [Order ℚ]

/--
Two rational numbers are equivalent exactly when the sign of their difference
is zero.

This lemma is mainly useful to support the proof of `order_trichotomy`.

**Property and proof intuition**: We already know that rational numbers are
equivalent when their difference is zero (`sub_eqv_zero_iff_eqv`); combine that
with the proof that the `sgn` of zero is zero.
-/
theorem eqv_sgn {p q : ℚ} : p ≃ q ↔ sgn (p - q) ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≃ q)
    show sgn (p - q) ≃ 0
    have : p - q ≃ 0 := sub_eqv_zero_iff_eqv.mpr ‹p ≃ q›
    have : sgn (p - q) ≃ 0 := sgn_zero.mp this
    exact this
  case mpr =>
    intro (_ : sgn (p - q) ≃ 0)
    show p ≃ q
    have : p - q ≃ 0 := sgn_zero.mpr ‹sgn (p - q) ≃ 0›
    have : p ≃ q := sub_eqv_zero_iff_eqv.mp this
    exact this

/--
A rational number is greater than another exactly when subtracting the latter
from the former yields a positive number; i.e. a sign of one.

**Property and proof intuition**: This is equivalent to the `lt_sgn` axiom, but
with the operands swapped. Swapping a subtraction negates its result, thus the
sign value is `1` instead of `-1`.
-/
theorem gt_sgn {p q : ℚ} : p > q ↔ sgn (p - q) ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : p > q)
    show sgn (p - q) ≃ 1
    have : q < p := ‹p > q›
    have : sgn (q - p) ≃ -1 := lt_sgn.mp this
    have : sgn (p - q) ≃ 1 := calc
      sgn (p - q)    ≃ _ := sgn_subst (eqv_symm neg_sub)
      sgn (-(q - p)) ≃ _ := sgn_compat_neg
      (-sgn (q - p)) ≃ _ := AA.subst₁ ‹sgn (q - p) ≃ -1›
      (-(-1))        ≃ _ := Integer.neg_involutive
      1              ≃ _ := Rel.refl
    exact this
  case mpr =>
    intro (_ : sgn (p - q) ≃ 1)
    show p > q
    have : sgn (q - p) ≃ -1 := calc
      sgn (q - p)    ≃ _ := sgn_subst (eqv_symm neg_sub)
      sgn (-(p - q)) ≃ _ := sgn_compat_neg
      (-sgn (p - q)) ≃ _ := AA.subst₁ ‹sgn (p - q) ≃ 1›
      (-1)           ≃ _ := Rel.refl
    have : q < p := lt_sgn.mpr this
    have : p > q := this
    exact this

/--
A rational number is greater than or equivalent to another when subtracting the
latter from the former gives a non-negative result, i.e. its sign is not minus
one.

**Property and proof intuition**: This is equivalent to the `le_sgn` axiom, but
with the operands swapped. Swapping a subtraction negates its result, thus the
sign value is `-1` instead of `1`.
-/
theorem ge_sgn {p q : ℚ} : p ≥ q ↔ sgn (p - q) ≄ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≥ q) (_ : sgn (p - q) ≃ -1)
    show False
    have : q ≤ p := ‹p ≥ q›
    have : sgn (q - p) ≄ 1 := le_sgn.mp this
    have : sgn (q - p) ≃ 1 := calc
      sgn (q - p)    ≃ _ := sgn_subst (eqv_symm neg_sub)
      sgn (-(p - q)) ≃ _ := sgn_compat_neg
      (-sgn (p - q)) ≃ _ := AA.subst₁ ‹sgn (p - q) ≃ -1›
      (-(-1))        ≃ _ := Integer.neg_involutive
      1              ≃ _ := Rel.refl
    exact absurd ‹sgn (q - p) ≃ 1› ‹sgn (q - p) ≄ 1›
  case mpr =>
    intro (_ : sgn (p - q) ≄ -1)
    show p ≥ q
    have : sgn (q - p) ≄ 1 := by
      intro (_ : sgn (q - p) ≃ 1)
      show False
      have : sgn (p - q) ≃ -1 := calc
        sgn (p - q)    ≃ _ := sgn_subst (eqv_symm neg_sub)
        sgn (-(q - p)) ≃ _ := sgn_compat_neg
        (-sgn (q - p)) ≃ _ := AA.subst₁ ‹sgn (q - p) ≃ 1›
        (-1)           ≃ _ := Rel.refl
      exact absurd ‹sgn (p - q) ≃ -1› ‹sgn (p - q) ≄ -1›
    have : q ≤ p := le_sgn.mpr this
    have : p ≥ q := this
    exact this

/--
A rational number is greater than or equivalent to zero exactly when its sign
is nonnegative.

**Property intuition**: This shows two equivalent ways of saying that the sign
of a number is positive or zero.

**Proof intuition**: This is a corollary of `ge_sgn`.
-/
theorem ge_zero_sgn {p : ℚ} : p ≥ 0 ↔ sgn p ≄ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≥ 0)
    show sgn p ≄ -1
    have : sgn (p - 0) ≄ -1 := ge_sgn.mp ‹p ≥ 0›
    have : sgn (p - 0) ≃ sgn p := sgn_subst sub_zero
    have : sgn p ≄ -1 := AA.neqv_substL this ‹sgn (p - 0) ≄ -1›
    exact this
  case mpr =>
    intro (_ : sgn p ≄ -1)
    show p ≥ 0
    have : sgn p ≃ sgn (p - 0) := sgn_subst (eqv_symm sub_zero)
    have : sgn (p - 0) ≄ -1 := AA.neqv_substL this ‹sgn p ≄ -1›
    have : p ≥ 0 := ge_sgn.mpr this
    exact this

/--
The ordering of any two rational numbers must be in exactly one of three
states: less than, equivalent to, or greater than.

**Property intuition**: This property holds for all total orders, and we expect
the rationals to have a total order because the integers do.

**Proof intuition**: The ordering relations can all be defined in terms of the
sign of the difference of their operands, so take the trichotomy of sign values
and translate it.
-/
theorem order_trichotomy
    (p q : ℚ) : AA.ExactlyOneOfThree (p < q) (p ≃ q) (p > q)
    := by
  show AA.ExactlyOneOfThree (p < q) (p ≃ q) (p > q)
  let spq := sgn (p - q)

  have : AA.OneOfThree (spq ≃ 0) (spq ≃ 1) (spq ≃ -1) := sgn_trichotomy (p - q)
  have : AA.OneOfThree (p ≃ q) (p > q) (p < q) :=
    this.map eqv_sgn.mpr gt_sgn.mpr lt_sgn.mpr
  have atLeastOne : AA.OneOfThree (p < q) (p ≃ q) (p > q) := this.rotR

  have : ¬AA.TwoOfThree (spq ≃ 0) (spq ≃ 1) (spq ≃ -1) :=
    Integer.signs_distinct
  have : ¬AA.TwoOfThree (p ≃ q) (p > q) (p < q) :=
    mt (AA.TwoOfThree.map eqv_sgn.mp gt_sgn.mp lt_sgn.mp) this
  have atMostOne : ¬AA.TwoOfThree (p < q) (p ≃ q) (p > q) :=
    mt AA.TwoOfThree.rotL this

  exact AA.ExactlyOneOfThree.mk atLeastOne atMostOne

/--
Make the "or" explicit in "less than or equivalent to".

**Proof intuition**: Use order trichotomy and the underlying `sgn` definition
of order to rule out the `p > q` case and leave the remaining two.
-/
theorem le_cases {p q : ℚ} : p ≤ q ↔ p < q ∨ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≤ q)
    show p < q ∨ p ≃ q
    have : AA.OneOfThree (p < q) (p ≃ q) (p > q) :=
      (order_trichotomy p q).atLeastOne
    match this with
    | AA.OneOfThree.first (_ : p < q) =>
      have : p < q ∨ p ≃ q := Or.inl ‹p < q›
      exact this
    | AA.OneOfThree.second (_ : p ≃ q) =>
      have : p < q ∨ p ≃ q := Or.inr ‹p ≃ q›
      exact this
    | AA.OneOfThree.third (_ : p > q) =>
      have : sgn (p - q) ≃ 1 := gt_sgn.mp ‹p > q›
      have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
      exact absurd ‹sgn (p - q) ≃ 1› ‹sgn (p - q) ≄ 1›
  case mpr =>
    intro (_ : p < q ∨ p ≃ q)
    show p ≤ q
    have : sgn (p - q) ≄ 1 := by
      intro (_ : sgn (p - q) ≃ 1)
      show False
      have : p > q := gt_sgn.mpr ‹sgn (p - q) ≃ 1›
      have not_two : ¬AA.TwoOfThree (p < q) (p ≃ q) (p > q) :=
        (order_trichotomy p q).atMostOne
      match ‹p < q ∨ p ≃ q› with
      | Or.inl (_ : p < q) =>
        have two : AA.TwoOfThree (p < q) (p ≃ q) (p > q) :=
          AA.TwoOfThree.oneAndThree ‹p < q› ‹p > q›
        exact absurd two not_two
      | Or.inr (_ : p ≃ q) =>
        have two : AA.TwoOfThree (p < q) (p ≃ q) (p > q) :=
          AA.TwoOfThree.twoAndThree ‹p ≃ q› ‹p > q›
        exact absurd two not_two
    have : p ≤ q := le_sgn.mpr this
    exact this

/--
Make the "or" explicit in "greater than or equivalent to".

**Proof intuition**: Use `le_cases` with some adjustments to swap operands.
-/
theorem ge_cases {p q : ℚ} : p ≥ q ↔ p > q ∨ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p ≥ q)
    show p > q ∨ p ≃ q
    have : q ≤ p := ‹p ≥ q›
    have : q < p ∨ q ≃ p := le_cases.mp this
    match this with
    | Or.inl (_ : q < p) =>
      have : p > q := ‹q < p›
      have : p > q ∨ p ≃ q := Or.inl this
      exact this
    | Or.inr (_ : q ≃ p) =>
      have : p ≃ q := eqv_symm ‹q ≃ p›
      have : p > q ∨ p ≃ q := Or.inr this
      exact this
  case mpr =>
    intro (_ : p > q ∨ p ≃ q)
    show p ≥ q
    have : q < p ∨ q ≃ p :=
      match ‹p > q ∨ p ≃ q› with
      | Or.inl (_ : p > q) =>
        have : q < p := ‹p > q›
        Or.inl this
      | Or.inr (_ : p ≃ q) =>
        have : q ≃ p := eqv_symm ‹p ≃ q›
        Or.inr this
    have : q ≤ p := le_cases.mpr this
    have : p ≥ q := this
    exact this

/--
The _less than_ relation for rational numbers is transitive.

**Property intuition**: This is a required property for any totally ordered
type.

**Proof intuition**: Convert the input relations to `sgn`s of differences.
We know the sum of the differences must have the same `sgn`. The sum
telescopes, leaving only the first and last value, giving us the result.
-/
theorem lt_trans {p q r : ℚ} : p < q → q < r → p < r := by
  intro (_ : p < q) (_ : q < r)
  show p < r
  have : sgn (p - q) ≃ -1 := lt_sgn.mp ‹p < q›
  have : sgn (q - r) ≃ -1 := lt_sgn.mp ‹q < r›
  have : sgn ((p - q) + (q - r)) ≃ -1 :=
    add_preserves_sign ‹sgn (p - q) ≃ -1› ‹sgn (q - r) ≃ -1›
  have : sgn (p - r) ≃ -1 := calc
    sgn (p - r)             ≃ _ := sgn_subst (eqv_symm add_sub_telescope)
    sgn ((p - q) + (q - r)) ≃ _ := ‹sgn ((p - q) + (q - r)) ≃ -1›
    (-1)                    ≃ _ := Rel.refl
  have : p < r := lt_sgn.mpr ‹sgn (p - r) ≃ -1›
  exact this

end Lean4Axiomatic.Rational
