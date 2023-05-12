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
A rational number is always less than or equivalent to itself.

In other words, _less than or equivalent to_ is a reflexive relation.

**Property and proof intuition**: Every rational number is equivalent to
itself, and thus is less than _or_ equivalent to itself as well.
-/
theorem le_refl {p : ℚ} : p ≤ p := by
  have : p ≃ p := eqv_refl
  have : p ≤ p := le_cases.mpr (Or.inr this)
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

instance trans_lt_lt_lt_inst : Trans (α := ℚ) (· < ·) (· < ·) (· < ·) := {
  trans := lt_trans
}

/--
The _greater than_ relation for rational numbers is transitive.

**Property intuition**: This is a required property for any totally ordered
type.

**Proof intuition**: Interpret _greater than_ as _less than_ and use
`lt_trans`.
-/
theorem gt_trans {p q r : ℚ} : p > q → q > r → p > r := by
  intro (_ : q < p) (_ : r < q)
  show r < p
  exact lt_trans ‹r < q› ‹q < p›

instance trans_gt_gt_gt_inst : Trans (α := ℚ) (· > ·) (· > ·) (· > ·) := {
  trans := gt_trans
}

/--
Replace _less than_'s left-hand operand with an equivalent value.

**Property intuition**: This must hold for _less than_ to be a valid relation
on rational numbers.

**Proof intuition**: Expand _less than_ into its `sgn`-of-difference form;
those operations allow substitution so _less than_ does as well.
-/
theorem lt_substL_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ < q → p₂ < q := by
  intro (_ : p₁ ≃ p₂) (_ : p₁ < q)
  show p₂ < q
  have : sgn (p₁ - q) ≃ -1 := lt_sgn.mp ‹p₁ < q›
  have : sgn (p₂ - q) ≃ -1 := calc
    sgn (p₂ - q) ≃ _ := sgn_subst (sub_substL (eqv_symm ‹p₁ ≃ p₂›))
    sgn (p₁ - q) ≃ _ := ‹sgn (p₁ - q) ≃ -1›
    (-1)         ≃ _ := Rel.refl
  have : p₂ < q := lt_sgn.mpr this
  exact this

/--
Corollary of `lt_substL_eqv` to support transitivity of equivalence and
_less than_.
-/
theorem trans_eqv_lt_lt {p₁ p₂ q : ℚ} : p₂ ≃ p₁ → p₁ < q → p₂ < q := by
  intro (_ : p₂ ≃ p₁) (_ : p₁ < q)
  show p₂ < q
  exact lt_substL_eqv (eqv_symm ‹p₂ ≃ p₁›) ‹p₁ < q›

instance trans_eqv_lt_lt_inst : Trans (α := ℚ) (· ≃ ·) (· < ·) (· < ·) := {
  trans := trans_eqv_lt_lt
}

/--
Replace _less than_'s right-hand operand with an equivalent value.

**Property intuition**: This must hold for _less than_ to be a valid relation
on rational numbers.

**Proof intuition**: Expand _less than_ into its `sgn`-of-difference form;
those operations allow substitution so _less than_ does as well.
-/
theorem lt_substR_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q < p₁ → q < p₂ := by
  intro (_ : p₁ ≃ p₂) (_ : q < p₁)
  show q < p₂
  have : sgn (q - p₁) ≃ -1 := lt_sgn.mp ‹q < p₁›
  have : sgn (q - p₂) ≃ -1 := calc
    sgn (q - p₂) ≃ _ := sgn_subst (sub_substR (eqv_symm ‹p₁ ≃ p₂›))
    sgn (q - p₁) ≃ _ := ‹sgn (q - p₁) ≃ -1›
    (-1)         ≃ _ := Rel.refl
  have : q < p₂ := lt_sgn.mpr this
  exact this

/--
Corollary of `lt_substR_eqv` to support transitivity of _less than_ and
equivalence.
-/
theorem trans_lt_eqv_lt {p₁ p₂ q : ℚ} : q < p₁ → p₁ ≃ p₂ → q < p₂ := by
  intro (_ : q < p₁) (_ : p₁ ≃ p₂)
  show q < p₂
  exact lt_substR_eqv ‹p₁ ≃ p₂› ‹q < p₁›

instance trans_lt_eqv_lt_inst : Trans (α := ℚ) (· < ·) (· ≃ ·) (· < ·) := {
  trans := trans_lt_eqv_lt
}

/--
Corollary of `trans_lt_eqv_lt` to support transitivity of equivalence and
_greater than_.
-/
theorem trans_eqv_gt_gt {p₁ p₂ q : ℚ} : p₂ ≃ p₁ → p₁ > q → p₂ > q := by
  intro (_ : p₂ ≃ p₁) (_ : q < p₁)
  show q < p₂
  exact trans_lt_eqv_lt ‹q < p₁› (eqv_symm ‹p₂ ≃ p₁›)

instance trans_eqv_gt_gt_inst : Trans (α := ℚ) (· ≃ ·) (· > ·) (· > ·) := {
  trans := trans_eqv_gt_gt
}

/--
Corollary of `trans_eqv_lt_lt` to support transitivity of _greater than_ and
equivalence.
-/
theorem trans_gt_eqv_gt {p₁ p₂ q : ℚ} : q > p₁ → p₁ ≃ p₂ → q > p₂ := by
  intro (_ : p₁ < q) (_ : p₁ ≃ p₂)
  show p₂ < q
  exact trans_eqv_lt_lt (eqv_symm ‹p₁ ≃ p₂›) ‹p₁ < q›

instance trans_gt_eqv_gt_inst : Trans (α := ℚ) (· > ·) (· ≃ ·) (· > ·) := {
  trans := trans_gt_eqv_gt
}

/--
Replace _less than or equivalent to_'s left-hand operand with an equivalent
value.

**Property intuition**: This must hold for _less than or equivalent to_ to be a
valid relation on rational numbers.

**Proof intuition**: Expand _less than or equivalent to_ into its
`sgn`-of-difference form; those operations allow substitution so
_less than or equivalent to_ does as well.
-/
theorem le_substL_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ ≤ q → p₂ ≤ q := by
  intro (_ : p₁ ≃ p₂) (_ : p₁ ≤ q)
  show p₂ ≤ q
  have : sgn (p₁ - q) ≄ 1 := le_sgn.mp ‹p₁ ≤ q›
  have : sgn (p₁ - q) ≃ sgn (p₂ - q) := sgn_subst (sub_substL ‹p₁ ≃ p₂›)
  have : sgn (p₂ - q) ≄ 1 := AA.neqv_substL this ‹sgn (p₁ - q) ≄ 1›
  have : p₂ ≤ q := le_sgn.mpr this
  exact this

/--
Corollary of `le_substL_eqv` to support transitivity of equivalence and
_less than or equivalent to_.
-/
theorem trans_eqv_le_le {p₁ p₂ q : ℚ} : p₂ ≃ p₁ → p₁ ≤ q → p₂ ≤ q := by
  intro (_ : p₂ ≃ p₁) (_ : p₁ ≤ q)
  show p₂ ≤ q
  exact le_substL_eqv (eqv_symm ‹p₂ ≃ p₁›) ‹p₁ ≤ q›

instance trans_eqv_le_le_inst : Trans (α := ℚ) (· ≃ ·) (· ≤ ·) (· ≤ ·) := {
  trans := trans_eqv_le_le
}

/--
Replace _less than or equivalent to_'s right-hand operand with an equivalent
value.

**Property intuition**: This must hold for _less than or equivalent to_ to be a
valid relation on rational numbers.

**Proof intuition**: Expand _less than or equivalent to_ into its
`sgn`-of-difference form; those operations allow substitution so
_less than or equivalent to_ does as well.
-/
theorem le_substR_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q ≤ p₁ → q ≤ p₂ := by
  intro (_ : p₁ ≃ p₂) (_ : q ≤ p₁)
  show q ≤ p₂
  have : sgn (q - p₁) ≄ 1 := le_sgn.mp ‹q ≤ p₁›
  have : sgn (q - p₁) ≃ sgn (q - p₂) := sgn_subst (sub_substR ‹p₁ ≃ p₂›)
  have : sgn (q - p₂) ≄ 1 := AA.neqv_substL this ‹sgn (q - p₁) ≄ 1›
  have : q ≤ p₂ := le_sgn.mpr this
  exact this

/--
Corollary of `le_substR_eqv` to support transitivity of
_less than or equivalent to_ and equivalence.
-/
theorem trans_le_eqv_le {p₁ p₂ q : ℚ} : q ≤ p₁ → p₁ ≃ p₂ → q ≤ p₂ := by
  intro (_ : q ≤ p₁) (_ : p₁ ≃ p₂)
  show q ≤ p₂
  exact le_substR_eqv ‹p₁ ≃ p₂› ‹q ≤ p₁›

instance trans_le_eqv_le_inst : Trans (α := ℚ) (· ≤ ·) (· ≃ ·) (· ≤ ·) := {
  trans := trans_le_eqv_le
}

/--
Corollary of `trans_le_eqv_le` to support transitivity of equivalence and
_greater than or equivalent to_.
-/
theorem trans_eqv_ge_ge {p₁ p₂ q : ℚ} : p₂ ≃ p₁ → p₁ ≥ q → p₂ ≥ q := by
  intro (_ : p₂ ≃ p₁) (_ : q ≤ p₁)
  show q ≤ p₂
  exact trans_le_eqv_le ‹q ≤ p₁› (eqv_symm ‹p₂ ≃ p₁›)

instance trans_eqv_ge_ge_inst : Trans (α := ℚ) (· ≃ ·) (· ≥ ·) (· ≥ ·) := {
  trans := trans_eqv_ge_ge
}

/--
Corollary of `trans_eqv_le_le` to support transitivity of _greater than or
equivalent to_ and equivalence.
-/
theorem trans_ge_eqv_ge {p₁ p₂ q : ℚ} : q ≥ p₁ → p₁ ≃ p₂ → q ≥ p₂ := by
  intro (_ : p₁ ≤ q) (_ : p₁ ≃ p₂)
  show p₂ ≤ q
  exact trans_eqv_le_le (eqv_symm ‹p₁ ≃ p₂›) ‹p₁ ≤ q›

instance trans_ge_eqv_ge_inst : Trans (α := ℚ) (· ≥ ·) (· ≃ ·) (· ≥ ·) := {
  trans := trans_ge_eqv_ge
}

/--
Merge two _less than or equivalent to_ relations on a common "midpoint" (i.e.,
_less than or equivalent to_ is transitive).

**Property intuition**: This allows reasoning about ordering to be extended to
values that are "further apart". It's fundamental to the meaning of _ordering_.

**Proof intuition**: Split each input relation into its _less than_ case and
its equivalence case. Delegate to a previous transitivity result for each
combination of cases. Note that this turns out to be easier than expanding the
relation into its `sgn`-based definition, because that involves a `· ≄ ·`
operation which is more difficult to deal with.
-/
theorem le_trans {p q r : ℚ} : p ≤ q → q ≤ r → p ≤ r := by
  intro (_ : p ≤ q) (_ : q ≤ r)
  show p ≤ r
  have : p < q ∨ p ≃ q := le_cases.mp ‹p ≤ q›
  have : q < r ∨ q ≃ r := le_cases.mp ‹q ≤ r›
  match And.intro ‹p < q ∨ p ≃ q› ‹q < r ∨ q ≃ r› with
  | (And.intro (Or.inl (_ : p < q)) (Or.inl (_ : q < r))) =>
    have : p < r := lt_trans ‹p < q› ‹q < r›
    have : p ≤ r := le_cases.mpr (Or.inl this)
    exact this
  | (And.intro (Or.inl (_ : p < q)) (Or.inr (_ : q ≃ r))) =>
    have : p < r := trans_lt_eqv_lt ‹p < q› ‹q ≃ r›
    have : p ≤ r := le_cases.mpr (Or.inl this)
    exact this
  | (And.intro (Or.inr (_ : p ≃ q)) (Or.inl (_ : q < r))) =>
    have : p < r := trans_eqv_lt_lt ‹p ≃ q› ‹q < r›
    have : p ≤ r := le_cases.mpr (Or.inl this)
    exact this
  | (And.intro (Or.inr (_ : p ≃ q)) (Or.inr (_ : q ≃ r))) =>
    have : p ≃ r := eqv_trans ‹p ≃ q› ‹q ≃ r›
    have : p ≤ r := le_cases.mpr (Or.inr this)
    exact this

instance trans_le_le_le_inst : Trans (α := ℚ) (· ≤ ·) (· ≤ ·) (· ≤ ·) := {
  trans := le_trans
}

/--
Merge two _greater than or equivalent to_ relations on a common "midpoint"
(i.e., _greater than or equivalent to_ is transitive).

**Property intuition**: This allows reasoning about ordering to be extended to
values that are "further apart". It's fundamental to the meaning of _ordering_.

**Proof intuition**: Interpret _greater than or equivalent to_ as _less than or
equivalent to_ and use `le_trans`.
-/
theorem ge_trans {p q r : ℚ} : p ≥ q → q ≥ r → p ≥ r := by
  intro (_ : q ≤ p) (_ : r ≤ q)
  show r ≤ p
  exact le_trans ‹r ≤ q› ‹q ≤ p›

instance trans_ge_ge_ge_inst : Trans (α := ℚ) (· ≥ ·) (· ≥ ·) (· ≥ ·) := {
  trans := ge_trans
}

/--
The largest sign value is one.

**Property and proof intuition**: The three possible sign values are `-1`, `0`,
and `1`. Show that each of these is less than or equal to `1`.
-/
theorem sgn_max {p : ℚ} : sgn p ≤ 1 := by
  have : AA.OneOfThree (sgn p ≃ 0) (sgn p ≃ 1) (sgn p ≃ -1) := sgn_trichotomy p
  match this with
  | AA.OneOfThree.first (_ : sgn p ≃ 0) =>
    have : (0 : ℤ) < 1 := Integer.zero_lt_one
    have : (0 : ℤ) ≤ 1 := Integer.le_iff_lt_or_eqv.mpr (Or.inl this)
    have : sgn p ≤ 1 := Integer.le_substL_eqv (Rel.symm ‹sgn p ≃ 0›) this
    exact this
  | AA.OneOfThree.second (_ : sgn p ≃ 1) =>
    have : (1 : ℤ) ≤ 1 := Integer.le_refl
    have : sgn p ≤ 1 := Integer.le_substL_eqv (Rel.symm ‹sgn p ≃ 1›) this
    exact this
  | AA.OneOfThree.third (_ : sgn p ≃ -1) =>
    have : (-1 : ℤ) < 0 := Integer.neg_one_lt_zero
    have : (0 : ℤ) < 1 := Integer.zero_lt_one
    have : (-1 : ℤ) < 1 := Integer.lt_trans ‹(-1 : ℤ) < 0› ‹(0 : ℤ) < 1›
    have : (-1 : ℤ) ≤ 1 := Integer.le_iff_lt_or_eqv.mpr (Or.inl this)
    have : sgn p ≤ 1 := Integer.le_substL_eqv (Rel.symm ‹sgn p ≃ -1›) this
    exact this

/--
The smallest sign value is negative one.

**Proof intuition**: Use `sgn_max` on the negation of the input number, then
transform algebraically to show the result.
-/
theorem sgn_min {p : ℚ} : sgn p ≥ -1 := by
  have : sgn (-p) ≤ 1 := sgn_max
  have : -(sgn (-p)) ≥ -1 := Integer.le_neg_flip.mp this
  have : -(-(sgn p)) ≥ -1 :=
    Integer.le_substR_eqv (AA.subst₁ sgn_compat_neg) this
  have : sgn p ≥ -1 := Integer.le_substR_eqv Integer.neg_involutive this
  exact this

/--
Add the same value on the right to both operands of
_less than or equivalent to_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem le_substL_add {p₁ p₂ q : ℚ} : p₁ ≤ p₂ → p₁ + q ≤ p₂ + q := by
  intro (_ : p₁ ≤ p₂)
  show p₁ + q ≤ p₂ + q
  have : sgn (p₁ - p₂) ≄ 1 := le_sgn.mp ‹p₁ ≤ p₂›
  have : sgn ((p₁ + q) - (p₂ + q)) ≃ sgn (p₁ - p₂) := sgn_subst sub_cancelR_add
  have : sgn ((p₁ + q) - (p₂ + q)) ≄ 1 :=
    AA.neqv_substL (Rel.symm this) ‹sgn (p₁ - p₂) ≄ 1›
  have : p₁ + q ≤ p₂ + q := le_sgn.mpr this
  exact this

/--
Add the same value on the left to both operands of
_less than or equivalent to_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because addition
is commutative.
-/
theorem le_substR_add {p₁ p₂ q : ℚ} : p₁ ≤ p₂ → q + p₁ ≤ q + p₂ := by
  intro (_ : p₁ ≤ p₂)
  show q + p₁ ≤ q + p₂
  calc
    _ ≃ q + p₁ := eqv_refl
    _ ≃ p₁ + q := add_comm
    _ ≤ p₂ + q := le_substL_add ‹p₁ ≤ p₂›
    _ ≃ q + p₂ := add_comm

/--
Add the same value on the right to both operands of _less than_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem lt_substL_add {p₁ p₂ q : ℚ} : p₁ < p₂ → p₁ + q < p₂ + q := by
  intro (_ : p₁ < p₂)
  show p₁ + q < p₂ + q
  have : sgn (p₁ - p₂) ≃ -1 := lt_sgn.mp ‹p₁ < p₂›
  have : sgn ((p₁ + q) - (p₂ + q)) ≃ sgn (p₁ - p₂) := sgn_subst sub_cancelR_add
  have : sgn ((p₁ + q) - (p₂ + q)) ≃ -1 :=
    AA.eqv_substL (Rel.symm this) ‹sgn (p₁ - p₂) ≃ -1›
  have : p₁ + q < p₂ + q := lt_sgn.mpr this
  exact this

/--
Add the same value on the left to both operands of _less than_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because addition
is commutative.
-/
theorem lt_substR_add {p₁ p₂ q : ℚ} : p₁ < p₂ → q + p₁ < q + p₂ := by
  intro (_ : p₁ < p₂)
  show q + p₁ < q + p₂
  calc
    _ ≃ q + p₁ := eqv_refl
    _ ≃ p₁ + q := add_comm
    _ < p₂ + q := lt_substL_add ‹p₁ < p₂›
    _ ≃ q + p₂ := add_comm

/--
Multiply both operands of _less than_ by the same positive value on the right.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem lt_substL_mul_pos {p q r : ℚ} : sgn r ≃ 1 → p < q → p * r < q * r := by
  intro (_ : sgn r ≃ 1) (_ : p < q)
  show p * r < q * r
  have : sgn (p - q) ≃ -1 := lt_sgn.mp ‹p < q›
  have : sgn (p * r - q * r) ≃ sgn (p - q) :=
    sgn_sub_cancelR_mul_pos ‹sgn r ≃ 1›
  have : sgn (p * r - q * r) ≃ -1 :=
    AA.eqv_substL (Rel.symm this) ‹sgn (p - q) ≃ -1›
  have : p * r < q * r := lt_sgn.mpr this
  exact this

/--
Multiply both operands of _less than_ by the same positive value on the left.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem lt_substR_mul_pos {p q r : ℚ} : sgn r ≃ 1 → p < q → r * p < r * q := by
  intro (_ : sgn r ≃ 1) (_ : p < q)
  show r * p < r * q
  calc
    _ ≃ r * p := eqv_refl
    _ ≃ p * r := mul_comm
    _ < q * r := lt_substL_mul_pos ‹sgn r ≃ 1› ‹p < q›
    _ ≃ r * q := mul_comm

/--
Multiply both operands of _less than_ by the same negative value on the right,
reversing their ordering.

**Property intuition**: Scaling two values by the same negative factor reflects
them across zero.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem lt_substL_mul_neg
    {p q r : ℚ} : sgn r ≃ -1 → p < q → q * r < p * r
    := by
  intro (_ : sgn r ≃ -1) (_ : p < q)
  show q * r < p * r
  have : sgn (p - q) ≃ -1 := lt_sgn.mp ‹p < q›
  have : sgn (q * r - p * r) ≃ sgn (p - q) :=
    sgn_sub_cancelR_mul_neg ‹sgn r ≃ -1›
  have : sgn (q * r - p * r) ≃ -1 :=
    AA.eqv_substL (Rel.symm this) ‹sgn (p - q) ≃ -1›
  have : q * r < p * r := lt_sgn.mpr this
  exact this

/--
Multiply both operands of _less than_ by the same negative value on the left,
reversing their ordering.

**Property intuition**: Scaling two values by the same negative factor reflects
them across zero.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem lt_substR_mul_neg
    {p q r : ℚ} : sgn r ≃ -1 → p < q → r * q < r * p
    := by
  intro (_ : sgn r ≃ -1) (_ : p < q)
  show r * q < r * p
  calc
    _ ≃ r * q := eqv_refl
    _ ≃ q * r := mul_comm
    _ < p * r := lt_substL_mul_neg ‹sgn r ≃ -1› ‹p < q›
    _ ≃ r * p := mul_comm

/--
Multiply both operands of _less than or equivalent to_ by the same positive
value on the right.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem le_substL_mul_pos {p q r : ℚ} : sgn r ≃ 1 → p ≤ q → p * r ≤ q * r := by
  intro (_ : sgn r ≃ 1) (_ : p ≤ q)
  show p * r ≤ q * r
  have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
  have : sgn (p * r - q * r) ≃ sgn (p - q) :=
    sgn_sub_cancelR_mul_pos ‹sgn r ≃ 1›
  have : sgn (p * r - q * r) ≄ 1 :=
    AA.neqv_substL (Rel.symm this) ‹sgn (p - q) ≄ 1›
  have : p * r ≤ q * r := le_sgn.mpr this
  exact this

/--
Multiply both operands of _less than or equivalent to_ by the same positive
value on the left.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem le_substR_mul_pos {p q r : ℚ} : sgn r ≃ 1 → p ≤ q → r * p ≤ r * q := by
  intro (_ : sgn r ≃ 1) (_ : p ≤ q)
  show r * p ≤ r * q
  calc
    _ ≃ r * p := eqv_refl
    _ ≃ p * r := mul_comm
    _ ≤ q * r := le_substL_mul_pos ‹sgn r ≃ 1› ‹p ≤ q›
    _ ≃ r * q := mul_comm

/--
Multiply both operands of _less than or equivalent to_ by the same negative
value on the right, reversing their ordering.

**Property intuition**: Scaling two values by the same negative factor reflects
them across zero.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem le_substL_mul_neg
    {p q r : ℚ} : sgn r ≃ -1 → p ≤ q → q * r ≤ p * r
    := by
  intro (_ : sgn r ≃ -1) (_ : p ≤ q)
  show q * r ≤ p * r
  have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
  have : sgn (q * r - p * r) ≃ sgn (p - q) :=
    sgn_sub_cancelR_mul_neg ‹sgn r ≃ -1›
  have : sgn (q * r - p * r) ≄ 1 :=
    AA.neqv_substL (Rel.symm this) ‹sgn (p - q) ≄ 1›
  have : q * r ≤ p * r := le_sgn.mpr this
  exact this

/--
Multiply both operands of _less than or equivalent to_ by the same negative
value on the left, reversing their ordering.

**Property intuition**: Scaling two values by the same negative factor reflects
them across zero.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem le_substR_mul_neg
    {p q r : ℚ} : sgn r ≃ -1 → p ≤ q → r * q ≤ r * p
    := by
  intro (_ : sgn r ≃ -1) (_ : p ≤ q)
  show r * q ≤ r * p
  calc
    _ ≃ r * q := eqv_refl
    _ ≃ q * r := mul_comm
    _ ≤ p * r := le_substL_mul_neg ‹sgn r ≃ -1› ‹p ≤ q›
    _ ≃ r * p := mul_comm

/--
Negate both operands of _less than_, reversing their ordering.

**Property and proof intuition**: Follows directly from the substitution
property on _less than_ for multiplication by negative one.
-/
theorem lt_subst_neg {p₁ p₂ : ℚ} : p₁ < p₂ → -p₂ < -p₁ := by
  intro (_ : p₁ < p₂)
  show -p₂ < -p₁
  calc
    _ ≃ -p₂     := eqv_refl
    _ ≃ -1 * p₂ := eqv_symm mul_neg_one
    _ < -1 * p₁ := lt_substR_mul_neg sgn_neg_one ‹p₁ < p₂›
    _ ≃ -p₁     := mul_neg_one

/--
Negate both operands of _less than or equivalent to_, reversing their ordering.

**Property and proof intuition**: Follows directly from the substitution
property on _less than or equivalent to_ for multiplication by negative one.
-/
theorem le_subst_neg {p₁ p₂ : ℚ} : p₁ ≤ p₂ → -p₂ ≤ -p₁ := by
  intro (_ : p₁ ≤ p₂)
  show -p₂ ≤ -p₁
  calc
    _ ≃ -p₂     := eqv_refl
    _ ≃ -1 * p₂ := eqv_symm mul_neg_one
    _ ≤ -1 * p₁ := le_substR_mul_neg sgn_neg_one ‹p₁ ≤ p₂›
    _ ≃ -p₁     := mul_neg_one

/--
The maximum of a rational number times a sign value is reached when the sign is
from that number.

**Property intuition**: Multiplying a number by its own sign never changes its
magnitude, but it will always make it positive.

**Proof intuition**: Expand the ordering relation in the goal to its `sgn`
definition, which involves a negation. Assume the unnegated expression, with
the goal of reaching a contradiction. Transform the expression using properties
of `sgn` to obtain an equivalence of two sign values, and two possible values
for one of them. For each value, show that the expression simplifies to a
nonsensical inequality of a sign value.
-/
theorem mul_sgn_self_max {p q : ℚ} : p * sgn q ≤ p * sgn p := by
  apply le_sgn.mpr
  show sgn (p * sgn q - p * sgn p) ≄ 1
  intro (_ : sgn (p * sgn q - p * sgn p) ≃ 1)
  show False

  have : sgn (sgn q - sgn p) * sgn p ≃ sgn (p * sgn q - p * sgn p) := calc
    sgn (sgn q - sgn p) * sgn p
      ≃ _ := AA.comm
    sgn p * sgn (sgn q - sgn p)
      ≃ _ := AA.substR (Rel.symm sgn_from_integer)
    sgn p * sgn ((sgn q - sgn p : ℤ) : ℚ)
      ≃ _ := Rel.symm sgn_compat_mul
    sgn (p * ((sgn q - sgn p : ℤ) : ℚ))
      ≃ _ := sgn_subst (mul_substR sub_compat_from_integer)
    sgn (p * ((sgn q : ℚ) - (sgn p : ℚ)))
      ≃ _ := sgn_subst mul_distribL_sub
    sgn (p * sgn q - p * sgn p)
      ≃ _ := Rel.refl
  have : sgn (sgn q - sgn p) * sgn p ≃ 1 :=
    Rel.trans this ‹sgn (p * sgn q - p * sgn p) ≃ 1›

  have sqrt1_and_eqv := Integer.mul_sqrt1_eqv.mp this
  have : Integer.Sqrt1 (sgn p) := sqrt1_and_eqv.left
  have : sgn (sgn q - sgn p) ≃ sgn p := sqrt1_and_eqv.right
  have : sgn p ≃ 1 ∨ sgn p ≃ -1 :=
    Integer.sqrt1_cases.mp ‹Integer.Sqrt1 (sgn p)›

  match this with
  | Or.inl (_ : sgn p ≃ 1) =>
    have : 1 ≃ sgn p := Rel.symm ‹sgn p ≃ 1›
    have : sgn (sgn q - 1) ≃ 1 := calc
      sgn (sgn q - 1)     ≃ _ := Integer.sgn_subst (Integer.sub_substR this)
      sgn (sgn q - sgn p) ≃ _ := ‹sgn (sgn q - sgn p) ≃ sgn p›
      sgn p               ≃ _ := ‹sgn p ≃ 1›
      1                   ≃ _ := Rel.refl
    have : sgn q > 1 := Integer.gt_sgn.mpr this
    have : sgn q ≤ 1 := sgn_max
    exact Integer.le_gt_false this ‹sgn q > 1›
  | Or.inr (_ : sgn p ≃ -1) =>
    have : -1 ≃ sgn p := Rel.symm ‹sgn p ≃ -1›
    have : sgn (sgn q - (-1)) ≃ -1 := calc
      sgn (sgn q - (-1))  ≃ _ := Integer.sgn_subst (Integer.sub_substR this)
      sgn (sgn q - sgn p) ≃ _ := ‹sgn (sgn q - sgn p) ≃ sgn p›
      sgn p               ≃ _ := ‹sgn p ≃ -1›
      (-1)                ≃ _ := Rel.refl
    have : sgn q < -1 := Integer.lt_sgn.mpr this
    have : sgn q ≥ -1 := sgn_min
    exact Integer.lt_ge_false ‹sgn q < -1› this

end Lean4Axiomatic.Rational
