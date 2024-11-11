import Lean4Axiomatic.Order
import Lean4Axiomatic.Rational.Sign

/-! # Rational numbers: order -/

namespace Lean4Axiomatic.Rational

open Logic (AP iff_subst_covar or_mapL or_mapR)
open Signed (sgn)

/-! ## Axioms -/

/-- Operations pertaining to rational number order. -/
class Order.Ops (ℚ : Type) where
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
    where
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
    where
  toOps : Order.Ops ℚ
  toProps : Order.Props ℚ

attribute [instance] Order.toOps
attribute [instance] Order.toProps

/-! ## Derived properties -/

variable {ℕ ℤ ℚ : Type}
  [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ] [Sign ℚ]
  [Subtraction ℚ] [Order ℚ]

/--
A rational number is less than zero iff it has a sign of `-1`.

**Property intuition**: These are both descriptions of negative numbers.

**Proof intuition**: Special case of `lt_sgn`.
-/
theorem lt_zero_sgn {p : ℚ} : p < 0 ↔ sgn p ≃ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : p < 0)
    show sgn p ≃ -1
    calc
      _ ≃ sgn p       := Rel.refl
      _ ≃ sgn (p - 0) := by srw [←sub_zero]
      _ ≃ -1          := lt_sgn.mp ‹p < 0›
  case mpr =>
    intro (_ : sgn p ≃ -1)
    show p < 0
    have : sgn (p - 0) ≃ -1 := calc
      _ ≃ sgn (p - 0) := Rel.refl
      _ ≃ sgn p       := by srw [sub_zero]
      _ ≃ -1          := ‹sgn p ≃ -1›
    have : p < 0 := lt_sgn.mpr this
    exact this

/--
A rational number is greater than another exactly when subtracting the latter
from the former yields a positive number; i.e. a sign of one.

**Property and proof intuition**: This is equivalent to the `lt_sgn` axiom, but
with the operands swapped. Swapping a subtraction negates its result, thus the
sign value is `1` instead of `-1`.
-/
theorem gt_sgn {p q : ℚ} : p > q ↔ sgn (p - q) ≃ 1 := calc
  _ ↔ p > q               := Iff.rfl
  _ ↔ q < p               := Iff.rfl
  _ ↔ sgn (q - p) ≃ -1    := lt_sgn
  _ ↔ sgn (-(p - q)) ≃ -1 := by srw [←neg_sub]
  _ ↔ -sgn (p - q) ≃ -1   := by srw [sgn_compat_neg]
  _ ↔ sgn (p - q) ≃ 1     := Iff.intro Integer.neg_inject Integer.neg_subst

/--
A rational number is greater than zero iff it has a sign of `1`.

**Property intuition**: These are both descriptions of positive numbers.

**Proof intuition**: Special case of `gt_sgn`.
-/
theorem gt_zero_sgn {p : ℚ} : p > 0 ↔ sgn p ≃ 1 := calc
  _ ↔ p > 0           := Iff.rfl
  _ ↔ sgn (p - 0) ≃ 1 := gt_sgn
  _ ↔ sgn p ≃ 1       := by srw [sub_zero]

/-- The rational number two is positive. -/
theorem two_pos : (2:ℚ) > 0 := by
  have : sgn (2:ℚ) ≃ 1 := sgn_two
  have : (2:ℚ) > 0 := gt_zero_sgn.mpr ‹sgn (2:ℚ) ≃ 1›
  exact this

/--
Positive rationals are nonzero.

**Proof intuition**: Any nonzero rational has a nonzero sign, by the
contrapositive of `sgn_zero`. In particular, positive rationals have a sign of
`1`, thus they are nonzero.
-/
theorem pos_nonzero {p : ℚ} : p > 0 → p ≄ 0 := by
  intro (_ : p > 0)
  show p ≄ 0
  have : sgn p ≃ 1 := gt_zero_sgn.mp ‹p > 0›
  have : (1:ℤ) ≄ 0 := Integer.one_neqv_zero
  have : sgn p ≄ 0 := by prw [←‹sgn p ≃ 1›] ‹(1:ℤ) ≄ 0›
  have : p ≄ 0 := mt sgn_zero.mp ‹sgn p ≄ 0›
  exact this

/--
The product of two positive rational numbers is also positive.

**Property intuition**: Multiplying a positive value by another positive value
can shrink it towards zero or grow it towards infinity, but it can't make it
zero or negative.

**Proof intuition**: Express the greater-than relations using `sgn`; we need to
show that `sgn (p * q)` is equivalent to `1` when both `sgn p` and `sgn q` are
equivalent to `1`. Use `sgn_compat_mul` to factor `sgn (p * q)` into
`sgn p * sgn q`; this is equivalent to one because both factors are.
-/
theorem mul_preserves_pos {p q : ℚ} : p > 0 → q > 0 → p * q > 0 := by
  intro (_ : p > 0) (_ : q > 0)
  show p * q > 0
  have : sgn (p * q) ≃ 1 := calc
    _ = sgn (p * q)   := rfl
    _ ≃ sgn p * sgn q := sgn_compat_mul
    _ ≃ 1 * sgn q     := by srw [gt_zero_sgn.mp ‹p > 0›]
    _ ≃ sgn q         := AA.identL
    _ ≃ 1             := gt_zero_sgn.mp ‹q > 0›
  have : p * q > 0 := gt_zero_sgn.mpr ‹sgn (p * q) ≃ 1›
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
      sgn (q - p)    ≃ _ := by srw [←neg_sub]
      sgn (-(p - q)) ≃ _ := sgn_compat_neg
      (-sgn (p - q)) ≃ _ := by srw [‹sgn (p - q) ≃ -1›]
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
        sgn (p - q)    ≃ _ := by srw [←neg_sub]
        sgn (-(q - p)) ≃ _ := sgn_compat_neg
        (-sgn (q - p)) ≃ _ := by srw [‹sgn (q - p) ≃ 1›]
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
theorem ge_zero_sgn {p : ℚ} : p ≥ 0 ↔ sgn p ≄ -1 := calc
  _ ↔ p ≥ 0            := Iff.rfl
  _ ↔ sgn (p - 0) ≄ -1 := ge_sgn
  _ ↔ sgn p ≄ -1       := by srw [sub_zero]

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
Convert bidirectionally between a _not less than or equivalent to_ relation of
two rational numbers and a fact about their difference's sign value.

**Property intuition**: Another way of saying "not less than or equivalent to"
is "greater than".

**Proof intuition**: In the forward direction, _less than or equivalent to_ is
defined as a sign value not equivalent to one, so the logical negation of this
is a double negation of a sign value equivalent to one. But equivalence on
rational numbers is decidable, so we can eliminate the double negation. In the
reverse direction, obtain the sign value of _less than or equivalent to_ and
reach a contradiction with the other hypothesis.
-/
theorem neg_le_sgn {p q : ℚ} : ¬(p ≤ q) ↔ sgn (p - q) ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : ¬(p ≤ q))
    show sgn (p - q) ≃ 1
    have : ¬(sgn (p - q) ≄ 1) := mt le_sgn.mpr ‹¬(p ≤ q)›
    have : sgn (p - q) ≃ 1 := Decidable.of_not_not this
    exact this
  case mpr =>
    intro (_ : sgn (p - q) ≃ 1) (_ : p ≤ q)
    show False
    have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
    exact absurd ‹sgn (p - q) ≃ 1› ‹sgn (p - q) ≄ 1›

/--
The _less than_ relation on rational numbers is irreflexive.

**Property and proof intuition**: We already have `p ≃ p`, so by trichotomy we
can't also have `p < p`.
-/
theorem lt_irrefl {p : ℚ} : p ≮ p := by
  intro (_ : p < p)
  show False
  let TriSame := AA.TwoOfThree (p < p) (p ≃ p) (p > p)
  have : p ≃ p := eqv_refl
  have : TriSame := AA.TwoOfThree.oneAndTwo ‹p < p› ‹p ≃ p›
  have : ¬TriSame := (order_trichotomy p p).atMostOne
  exact absurd ‹TriSame› ‹¬TriSame›

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
@[refl]
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
Two rational numbers cannot be both _less than or equivalent to_ and _greater
than_ each other.

**Property and proof intuition**: Follows directly from trichotomy.
-/
theorem le_gt_false {p q : ℚ} : p ≤ q → p > q → False := by
  intro (_ : p ≤ q) (_ : p > q)
  show False
  let TwoOfThree := AA.TwoOfThree (p < q) (p ≃ q) (p > q)
  have : ¬TwoOfThree := (order_trichotomy p q).atMostOne
  have : p < q ∨ p ≃ q := le_cases.mp ‹p ≤ q›
  have : TwoOfThree :=
    match this with
    | Or.inl (_ : p < q) => AA.TwoOfThree.oneAndThree ‹p < q› ‹p > q›
    | Or.inr (_ : p ≃ q) => AA.TwoOfThree.twoAndThree ‹p ≃ q› ‹p > q›
  exact absurd ‹TwoOfThree› ‹¬TwoOfThree›

/--
There are two possibilities for a _less than or equivalent to_ relation between
rational numbers.

**Property and proof intuition**: From order trichotomy, we know that one
rational number can be less than, equivalent to, or greater than another. The
_less than_ case implies the first result possibility, the _greater than_ case
implies the second result possibility, and the _equivalent to_ case implies
either one.
-/
theorem le_dichotomy {p q : ℚ} : p ≤ q ∨ q ≤ p := by
  let OneOfThree := AA.OneOfThree (p < q) (p ≃ q) (p > q)
  have : OneOfThree := (order_trichotomy p q).atLeastOne
  match this with
  | AA.OneOfThree.first (_ : p < q) =>
    have : p < q ∨ p ≃ q := Or.inl ‹p < q›
    have : p ≤ q := le_cases.mpr this
    have : p ≤ q ∨ q ≤ p := Or.inl this
    exact this
  | AA.OneOfThree.second (_ : p ≃ q) =>
    have : p < q ∨ p ≃ q := Or.inr ‹p ≃ q›
    have : p ≤ q := le_cases.mpr this
    have : p ≤ q ∨ q ≤ p := Or.inl this
    exact this
  | AA.OneOfThree.third (_ : p > q) =>
    have : q < p ∨ q ≃ p := Or.inl ‹q < p›
    have : q ≤ p := le_cases.mpr this
    have : p ≤ q ∨ q ≤ p := Or.inr this
    exact this

/--
The _less than_ relation on rationals is consistent with its integer
equivalent.
-/
theorem lt_respects_from_integer {a b : ℤ} : a < b ↔ (a:ℚ) < (b:ℚ) := calc
  _ ↔ a < b                    := Iff.rfl
  -- ↓ begin key lines ↓
  _ ↔ sgn (a - b) ≃ -1         := Integer.lt_sgn
  _ ↔ sgn ((a - b : ℤ):ℚ) ≃ -1 := by srw [←sgn_from_integer]
  _ ↔ sgn ((a:ℚ) - (b:ℚ)) ≃ -1 := by srw [sub_compat_from_integer]
  -- ↑  end key lines  ↑
  _ ↔ (a:ℚ) < (b:ℚ)            := lt_sgn.symm

/-- The rational number two is greater than one. -/
theorem two_gt_one : (2:ℚ) > 1 :=
  have : (2:ℚ) = ((2:ℕ):ℚ) := rfl
  lt_respects_from_integer.mp Integer.two_gt_one

/--
Conversion between integers and rationals preserves the _less than or
equivalent to_ relation.
-/
theorem le_respects_from_integer {a b : ℤ} : a ≤ b ↔ (a:ℚ) ≤ (b:ℚ) := calc
  _ ↔ a ≤ b                   := Iff.rfl
  -- ↓ begin key lines ↓
  _ ↔ sgn (a - b) ≄ 1         := Integer.le_sgn
  _ ↔ sgn ((a - b : ℤ):ℚ) ≄ 1 := by srw [←sgn_from_integer]
  _ ↔ sgn ((a:ℚ) - (b:ℚ)) ≄ 1 := by srw [sub_compat_from_integer]
  -- ↑  end key lines  ↑
  _ ↔ (a:ℚ) ≤ (b:ℚ)           := le_sgn.symm

/--
One is greater than or equivalent to zero in the rationals.

**Property and proof intuition**: This is consistent with the integers.
-/
theorem one_ge_zero : (1:ℚ) ≥ 0 := by
  have : (1:ℤ) > 0 := Integer.zero_lt_one
  have : (1:ℚ) > 0 := lt_respects_from_integer.mp this
  have : (1:ℚ) ≥ 0 := ge_cases.mpr (Or.inl this)
  exact this

/--
Replace _less than_'s left-hand operand with an equivalent value.

**Property intuition**: This must hold for _less than_ to be a valid relation
on rational numbers.

**Proof intuition**: Expand _less than_ into its `sgn`-of-difference form;
those operations allow substitution so _less than_ does as well.
-/
@[gcongr]
theorem lt_substL_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ < q → p₂ < q := by
  intro (_ : p₁ ≃ p₂) (_ : p₁ < q)
  show p₂ < q
  have : sgn (p₁ - q) ≃ -1 := lt_sgn.mp ‹p₁ < q›
  have : sgn (p₂ - q) ≃ -1 := calc
    sgn (p₂ - q) ≃ _ := by srw [←‹p₁ ≃ p₂›]
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
  prw [←‹p₂ ≃ p₁›] ‹p₁ < q›

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
@[gcongr]
theorem lt_substR_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q < p₁ → q < p₂ := by
  intro (_ : p₁ ≃ p₂) (_ : q < p₁)
  show q < p₂
  have : sgn (q - p₁) ≃ -1 := lt_sgn.mp ‹q < p₁›
  have : sgn (q - p₂) ≃ -1 := calc
    sgn (q - p₂) ≃ _ := by srw [←‹p₁ ≃ p₂›]
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
  prw [‹p₁ ≃ p₂›] ‹q < p₁›

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
@[gcongr]
theorem le_substL_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ ≤ q → p₂ ≤ q := by
  intro (_ : p₁ ≃ p₂) (_ : p₁ ≤ q)
  show p₂ ≤ q
  have : sgn (p₁ - q) ≄ 1 := le_sgn.mp ‹p₁ ≤ q›
  have : sgn (p₂ - q) ≄ 1 := by prw [‹p₁ ≃ p₂›] this
  have : p₂ ≤ q           := le_sgn.mpr this
  exact this

/--
Corollary of `le_substL_eqv` to support transitivity of equivalence and
_less than or equivalent to_.
-/
theorem trans_eqv_le_le {p₁ p₂ q : ℚ} : p₂ ≃ p₁ → p₁ ≤ q → p₂ ≤ q := by
  intro (_ : p₂ ≃ p₁) (_ : p₁ ≤ q)
  show p₂ ≤ q
  prw [←‹p₂ ≃ p₁›] ‹p₁ ≤ q›

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
@[gcongr]
theorem le_substR_eqv {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q ≤ p₁ → q ≤ p₂ := by
  intro (_ : p₁ ≃ p₂) (_ : q ≤ p₁)
  show q ≤ p₂
  have : sgn (q - p₁) ≄ 1 := le_sgn.mp ‹q ≤ p₁›
  have : sgn (q - p₂) ≄ 1 := by prw [‹p₁ ≃ p₂›] ‹sgn (q - p₁) ≄ 1›
  have : q ≤ p₂ := le_sgn.mpr this
  exact this

/--
Corollary of `le_substR_eqv` to support transitivity of
_less than or equivalent to_ and equivalence.
-/
theorem trans_le_eqv_le {p₁ p₂ q : ℚ} : q ≤ p₁ → p₁ ≃ p₂ → q ≤ p₂ := by
  intro (_ : q ≤ p₁) (_ : p₁ ≃ p₂)
  show q ≤ p₂
  prw [‹p₁ ≃ p₂›] ‹q ≤ p₁›

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
The left-hand side of a _less than or equivalent to_ relation can be replaced
by an equivalent value, bidirectionally.
-/
@[gcongr]
theorem iff_substL_le {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → (p₁ ≤ q ↔ p₂ ≤ q) := by
  intro (_ : p₁ ≃ p₂)
  show p₁ ≤ q ↔ p₂ ≤ q
  exact Iff.intro (by prw [‹p₁ ≃ p₂›] ·) (by prw [←‹p₁ ≃ p₂›] ·)

/--
The right-hand side of a _less than or equivalent to_ relation can be replaced
by an equivalent value, bidirectionally.
-/
@[gcongr]
theorem iff_substR_le {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → (q ≤ p₁ ↔ q ≤ p₂) := by
  intro (_ : p₁ ≃ p₂)
  show q ≤ p₁ ↔ q ≤ p₂
  exact Iff.intro (by prw [‹p₁ ≃ p₂›] ·) (by prw [←‹p₁ ≃ p₂›] ·)

/--
The _less than or equivalent to_ relation on rational numbers is antisymmetric.

**Property and proof intuition**: Two numbers can't be both less than and
greater than each other, so the only option is for them to be equivalent.
-/
theorem le_antisymm {p q : ℚ} : p ≤ q → q ≤ p → p ≃ q := by
  intro (_ : p ≤ q) (_ : q ≤ p)
  show p ≃ q
  have : p < q ∨ p ≃ q := le_cases.mp ‹p ≤ q›
  match this with
  | Or.inl (_ : p < q) =>
    have : q < p ∨ q ≃ p := le_cases.mp ‹q ≤ p›
    match this with
    | Or.inl (_ : q < p) =>
      let Tri := AA.TwoOfThree (p < q) (p ≃ q) (p > q)
      have : Tri := AA.TwoOfThree.oneAndThree ‹p < q› ‹p > q›
      have : ¬Tri := (order_trichotomy p q).atMostOne
      exact absurd ‹Tri› ‹¬Tri›
    | Or.inr (_ : q ≃ p) =>
      exact eqv_symm ‹q ≃ p›
  | Or.inr (_ : p ≃ q) =>
    exact ‹p ≃ q›

/--
Add the same value on the left to both operands of
_less than or equivalent to_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Express the order relations on both sides of the iff via
their `sgn`-based definitions. Show that they are equivalent using algebra and
substitution.
-/
theorem le_addL_iff {p₁ p₂ q : ℚ} : p₁ ≤ p₂ ↔ q + p₁ ≤ q + p₂ := calc
  _ ↔ p₁ ≤ p₂                       := Iff.rfl
  _ ↔ sgn (p₁ - p₂) ≄ 1             := le_sgn
  _ ↔ sgn ((q + p₁) - (q + p₂)) ≄ 1 := by srw [←sub_cancelL_add]
  _ ↔ q + p₁ ≤ q + p₂               := le_sgn.symm

/--
Add the same value on the right to both operands of
_less than or equivalent to_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because addition
is commutative.
-/
theorem le_addR_iff {p₁ p₂ q : ℚ} : p₁ ≤ p₂ ↔ p₁ + q ≤ p₂ + q := calc
  _ ↔ p₁ ≤ p₂         := Iff.rfl
  _ ↔ q + p₁ ≤ q + p₂ := le_addL_iff
  _ ↔ p₁ + q ≤ p₂ + q := by srw [add_comm, add_comm]

/-- Corollary of `le_addR_iff` that's useful for congruence tactics. -/
@[gcongr]
abbrev le_substL_add {p₁ p₂ q : ℚ} : p₁ ≤ p₂ → p₁ + q ≤ p₂ + q := le_addR_iff.mp

/-- Corollary of `le_addL_iff` that's useful for congruence tactics. -/
@[gcongr]
abbrev le_substR_add {p₁ p₂ q : ℚ} : p₁ ≤ p₂ → q + p₁ ≤ q + p₂ := le_addL_iff.mp

/--
Add the same value on the right to both operands of _less than_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
@[gcongr]
theorem lt_substL_add {p₁ p₂ q : ℚ} : p₁ < p₂ → p₁ + q < p₂ + q := by
  intro (_ : p₁ < p₂)
  show p₁ + q < p₂ + q
  have : sgn ((p₁ + q) - (p₂ + q)) ≃ -1 := calc
    _ = sgn ((p₁ + q) - (p₂ + q)) := rfl
    _ ≃ sgn (p₁ - p₂)             := by srw [sub_cancelR_add]
    _ ≃ -1                        := lt_sgn.mp ‹p₁ < p₂›
  have : p₁ + q < p₂ + q := lt_sgn.mpr ‹sgn ((p₁ + q) - (p₂ + q)) ≃ -1›
  exact this

/--
Add the same value on the left to both operands of _less than_.

**Property intuition**: Shifting two values by the same amount doesn't change
their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because addition
is commutative.
-/
@[gcongr]
theorem lt_substR_add {p₁ p₂ q : ℚ} : p₁ < p₂ → q + p₁ < q + p₂ := by
  intro (_ : p₁ < p₂)
  show q + p₁ < q + p₂
  calc
    _ ≃ q + p₁ := eqv_refl
    _ ≃ p₁ + q := add_comm
    _ < p₂ + q := by srw [‹p₁ < p₂›]
    _ ≃ q + p₂ := add_comm

/--
Multiply both operands of _less than_ by the same positive value on the right.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem lt_substL_mul_pos {p q r : ℚ} : r > 0 → p < q → p * r < q * r := by
  intro (_ : r > 0) (_ : p < q)
  show p * r < q * r
  have : sgn r ≃ 1 := gt_zero_sgn.mp ‹r > 0›
  have : sgn (p * r - q * r) ≃ -1 := calc
    _ = sgn (p * r - q * r) := rfl
    _ ≃ sgn (p - q)         := sgn_sub_cancelR_mul_pos ‹sgn r ≃ 1›
    _ ≃ -1                  := lt_sgn.mp ‹p < q›
  have : p * r < q * r := lt_sgn.mpr ‹sgn (p * r - q * r) ≃ -1›
  exact this

/--
Multiply both operands of _less than_ by the same positive value on the left.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem lt_substR_mul_pos {p q r : ℚ} : r > 0 → p < q → r * p < r * q := by
  intro (_ : r > 0) (_ : p < q)
  show r * p < r * q
  calc
    _ ≃ r * p := eqv_refl
    _ ≃ p * r := mul_comm
    _ < q * r := lt_substL_mul_pos ‹r > 0› ‹p < q›
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
theorem lt_substL_mul_neg {p q r : ℚ} : r < 0 → q > p → q * r < p * r := by
  intro (_ : r < 0) (_ : p < q)
  show q * r < p * r
  have : sgn r ≃ -1 := lt_zero_sgn.mp ‹r < 0›
  have : sgn (q * r - p * r) ≃ -1 := calc
    _ = sgn (q * r - p * r) := rfl
    _ ≃ sgn (p - q)         := sgn_sub_cancelR_mul_neg ‹sgn r ≃ -1›
    _ ≃ -1                  := lt_sgn.mp ‹p < q›
  have : q * r < p * r := lt_sgn.mpr ‹sgn (q * r - p * r) ≃ -1›
  exact this

/--
Multiply both operands of _less than_ by the same negative value on the left,
reversing their ordering.

**Property intuition**: Scaling two values by the same negative factor reflects
them across zero.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem lt_substR_mul_neg {p q r : ℚ} : r < 0 → p < q → r * q < r * p := by
  intro (_ : r < 0) (_ : p < q)
  show r * q < r * p
  calc
    _ ≃ r * q := eqv_refl
    _ ≃ q * r := mul_comm
    _ < p * r := lt_substL_mul_neg ‹r < 0› ‹p < q›
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
theorem le_substL_mul_pos {p q r : ℚ} : r > 0 → p ≤ q → p * r ≤ q * r := by
  intro (_ : r > 0) (_ : p ≤ q)
  show p * r ≤ q * r
  have : sgn r ≃ 1 := gt_zero_sgn.mp ‹r > 0›
  have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
  have : sgn (p * r - q * r) ≄ 1 :=
    by prw [←sgn_sub_cancelR_mul_pos ‹sgn r ≃ 1›] this
  have : p * r ≤ q * r := le_sgn.mpr ‹sgn (p * r - q * r) ≄ 1›
  exact this

/--
Multiply both operands of _less than or equivalent to_ by the same positive
value on the left.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Follows from the opposite-handed version because
multiplication is commutative.
-/
theorem le_substR_mul_pos {p q r : ℚ} : r > 0 → p ≤ q → r * p ≤ r * q := by
  intro (_ : r > 0) (_ : p ≤ q)
  show r * p ≤ r * q
  calc
    _ ≃ r * p := eqv_refl
    _ ≃ p * r := mul_comm
    _ ≤ q * r := le_substL_mul_pos ‹r > 0› ‹p ≤ q›
    _ ≃ r * q := mul_comm

/--
Multiply both operands of _less than or equivalent to_ by the same nonnegative
factor on the right.

**Property and proof intuition**: If the factor is positive, then we've already
established the result. If the factor is zero, then the operands are scaled
down to zero and the result is true because they are equivalent.
-/
theorem le_substL_mul_nonneg {p q r : ℚ} : r ≥ 0 → p ≤ q → p * r ≤ q * r := by
  intro (_ : r ≥ 0) (_ : p ≤ q)
  show p * r ≤ q * r
  have : r > 0 ∨ r ≃ 0 := ge_cases.mp ‹r ≥ 0›
  match this with
  | Or.inl (_ : r > 0) =>
    have : p * r ≤ q * r := le_substL_mul_pos ‹r > 0› ‹p ≤ q›
    exact this
  | Or.inr (_ : r ≃ 0) =>
    calc
      _ = p * r := rfl
      _ ≃ p * 0 := by srw [‹r ≃ 0›]
      _ ≃ 0     := mul_absorbR
      _ ≃ q * 0 := eqv_symm mul_absorbR
      _ ≃ q * r := by srw [←‹r ≃ 0›]
      _ ≤ q * r := le_refl

/--
Multiply both operands of _less than or equivalent to_ by the same nonnegative
factor on the left.

**Property and proof intuition**: This is equivalent to the opposite-handed
version, but with the multiplications flipped around by commutativity.
-/
theorem le_substR_mul_nonneg {p q r : ℚ} : r ≥ 0 → p ≤ q → r * p ≤ r * q := by
  intro (_ : r ≥ 0) (_ : p ≤ q)
  show r * p ≤ r * q
  calc
    _ ≃ r * p := eqv_refl
    _ ≃ p * r := mul_comm
    _ ≤ q * r := le_substL_mul_nonneg ‹r ≥ 0› ‹p ≤ q›
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
theorem le_substL_mul_neg {p q r : ℚ} : r < 0 → p ≤ q → q * r ≤ p * r := by
  intro (_ : r < 0) (_ : p ≤ q)
  show q * r ≤ p * r
  have : sgn r ≃ -1 := lt_zero_sgn.mp ‹r < 0›
  have : sgn (p - q) ≄ 1 := le_sgn.mp ‹p ≤ q›
  have : sgn (q * r - p * r) ≄ 1 :=
    by prw [←sgn_sub_cancelR_mul_neg ‹sgn r ≃ -1›] this
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
theorem le_substR_mul_neg {p q r : ℚ} : r < 0 → p ≤ q → r * q ≤ r * p := by
  intro (_ : r < 0) (_ : p ≤ q)
  show r * q ≤ r * p
  calc
    _ ≃ r * q := eqv_refl
    _ ≃ q * r := mul_comm
    _ ≤ p * r := le_substL_mul_neg ‹r < 0› ‹p ≤ q›
    _ ≃ r * p := mul_comm

/--
Negative one is less than zero in the rationals.

**Property and proof intuition**: This is consistent with the integers.
-/
theorem neg_one_lt_zero : (-1:ℚ) < 0 := calc
  _ ≃ (-1:ℚ)     := eqv_refl
  _ ≃ ((-1:ℤ):ℚ) := eqv_symm neg_compat_from_integer
  _ < 0          := lt_respects_from_integer.mp Integer.neg_one_lt_zero

/--
Negate both operands of _less than_, reversing their ordering.

**Property and proof intuition**: Follows directly from the substitution
property on _less than_ for multiplication by negative one.
-/
@[gcongr]
theorem lt_subst_neg {p₁ p₂ : ℚ} : p₁ < p₂ → -p₂ < -p₁ := by
  intro (_ : p₁ < p₂)
  show -p₂ < -p₁
  calc
    _ ≃ -p₂     := eqv_refl
    _ ≃ -1 * p₂ := eqv_symm mul_neg_one
    _ < -1 * p₁ := lt_substR_mul_neg neg_one_lt_zero ‹p₁ < p₂›
    _ ≃ -p₁     := mul_neg_one

/--
Negate both operands of _less than or equivalent to_, reversing their ordering.

**Property and proof intuition**: Follows directly from the substitution
property on _less than or equivalent to_ for multiplication by negative one.
-/
@[gcongr]
theorem le_subst_neg {p₁ p₂ : ℚ} : p₁ ≤ p₂ → -p₂ ≤ -p₁ := by
  intro (_ : p₁ ≤ p₂)
  show -p₂ ≤ -p₁
  calc
    _ ≃ -p₂     := eqv_refl
    _ ≃ -1 * p₂ := eqv_symm mul_neg_one
    _ ≤ -1 * p₁ := le_substR_mul_neg neg_one_lt_zero ‹p₁ ≤ p₂›
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

  have : sgn (sgn q - sgn p) * sgn p ≃ 1 := calc
    _ = sgn (sgn q - sgn p) * sgn p         := rfl
    _ ≃ sgn p * sgn (sgn q - sgn p)         := AA.comm
    _ ≃ sgn p * sgn ((sgn q - sgn p : ℤ):ℚ) := by srw [←sgn_from_integer]
    _ ≃ sgn (p * ((sgn q - sgn p : ℤ):ℚ))   := Rel.symm sgn_compat_mul
    _ ≃ sgn (p * ((sgn q:ℚ) - (sgn p:ℚ)))   := by srw [sub_compat_from_integer]
    _ ≃ sgn (p * sgn q - p * sgn p)         := by srw [mul_distribL_sub]
    _ ≃ 1                                   := ‹sgn (p * sgn q - p * sgn p) ≃ 1›

  have sqrt1_and_eqv :=
    Integer.mul_sqrt1_eqv.mp ‹sgn (sgn q - sgn p) * sgn p ≃ 1›
  have : Integer.Sqrt1 (sgn p) := sqrt1_and_eqv.left
  have : sgn (sgn q - sgn p) ≃ sgn p := sqrt1_and_eqv.right
  have : sgn p ≃ 1 ∨ sgn p ≃ -1 :=
    Integer.sqrt1_cases.mp ‹Integer.Sqrt1 (sgn p)›

  match ‹sgn p ≃ 1 ∨ sgn p ≃ -1› with
  | Or.inl (_ : sgn p ≃ 1) =>
    have : sgn (sgn q - 1) ≃ 1 := calc
      _ = sgn (sgn q - 1)     := rfl
      _ ≃ sgn (sgn q - sgn p) := by srw [←‹sgn p ≃ 1›]
      _ ≃ sgn p               := ‹sgn (sgn q - sgn p) ≃ sgn p›
      _ ≃ 1                   := ‹sgn p ≃ 1›
    have : sgn q > 1 := Integer.gt_sgn.mpr ‹sgn (sgn q - 1) ≃ 1›
    have : sgn q ≤ 1 := sgn_max
    exact Integer.le_gt_false this ‹sgn q > 1›
  | Or.inr (_ : sgn p ≃ -1) =>
    have : sgn (sgn q - (-1)) ≃ -1 := calc
      _ = sgn (sgn q - (-1))  := rfl
      _ ≃ sgn (sgn q - sgn p) := by srw [←‹sgn p ≃ -1›]
      _ ≃ sgn p               := ‹sgn (sgn q - sgn p) ≃ sgn p›
      _ ≃ (-1)                := ‹sgn p ≃ -1›
    have : sgn q < -1 := Integer.lt_sgn.mpr this
    have : sgn q ≥ -1 := sgn_min
    exact Integer.lt_ge_false ‹sgn q < -1› this

/--
A lemma rewriting a difference's lower bound into a lower bound on its first
argument.

**Property and proof intuition**: The second argument of the difference can be
moved to the other side of the ordering relation via algebra.
-/
theorem le_diff_lower {ε p q : ℚ} : -ε ≤ q - p ↔ p - ε ≤ q := calc
  _ ↔     -ε ≤ q - p      := Iff.rfl
  _ ↔     -ε ≤ q + -p     := by srw [sub_add_neg]
  _ ↔ -ε + p ≤ q + -p + p := le_addR_iff
  _ ↔ -ε + p ≤ q          := by srw [add_assoc, add_inverseL, add_identR]
  _ ↔  p - ε ≤ q          := by srw [add_comm, ←sub_add_neg]

/--
A lemma rewriting a difference's upper bound into an upper bound on its first
argument.

**Property and proof intuition**: The second argument of the difference can be
moved to the other side of the ordering relation via algebra.
-/
theorem le_diff_upper {ε p q : ℚ} : q - p ≤ ε ↔ q ≤ p + ε := calc
  _ ↔      q - p ≤ ε     := Iff.rfl
  _ ↔     q + -p ≤ ε     := by srw [sub_add_neg]
  _ ↔ q + -p + p ≤ ε + p := le_addR_iff
  _ ↔          q ≤ ε + p := by srw [add_assoc, add_inverseL, add_identR]
  _ ↔          q ≤ p + ε := by srw [add_comm]

theorem not_ge_iff_lt {p q : ℚ} : ¬(p ≥ q) ↔ p < q := sorry

variable [Reciprocation ℚ] [Division ℚ]

/--
The comparison of reciprocals of two rational numbers gives the opposite result
as comparison of the original numbers, when both numbers have the same nonzero
sign.

**Property intuition**: `2 < 3`, but `1/2 > 1/3`.

**Proof intuition**: Simplify the subtraction of reciprocals into an expression
with a single division. Computing its sign converts the division into
multiplication. The former denominator is positive and drops out, leaving the
former numerator which gives the result.
-/
theorem sgn_sub_recip
    {p q : ℚ} (pq_pos : p * q > 0)
    : have : p * q ≄ 0 := pos_nonzero ‹p * q > 0›
      have : p ≄ 0 ∧ q ≄ 0 := mul_split_nonzero.mp ‹p * q ≄ 0›
      have : AP (p ≄ 0) := AP.mk ‹p ≄ 0 ∧ q ≄ 0›.1
      have : AP (q ≄ 0) := AP.mk ‹p ≄ 0 ∧ q ≄ 0›.2
      sgn (p⁻¹ - q⁻¹) ≃ sgn (q - p)
    := by
  intro _ _ (_ : AP (p ≄ 0)) (_ : AP (q ≄ 0))
  show sgn (p⁻¹ - q⁻¹) ≃ sgn (q - p)
  calc
    _ = sgn (p⁻¹ - q⁻¹)               := rfl
    _ ≃ sgn (1/p - 1/q)               := by srw [←div_identL, ←div_identL]
    _ ≃ sgn ((1 * q - p * 1)/(p * q)) := by srw [sub_fractions]
    _ ≃ sgn ((q - p)/(p * q))         := by srw [mul_identL, mul_identR]
    _ ≃ sgn (q - p) * sgn (p * q)     := sgn_div
    _ ≃ sgn (q - p) * 1               := by srw [gt_zero_sgn.mp ‹p * q > 0›]
    _ ≃ sgn (q - p)                   := AA.identR

variable [Induction.{1} ℚ]

/--
A rational number is greater than zero iff its sign is greater than zero.

**Property and proof intuition**: Rationals greater than zero have sign value
`1`; this is the only sign value that's greater than zero.
-/
theorem sgn_preserves_gt_zero {p : ℚ} : p > 0 ↔ sgn p > 0 := calc
  _ ↔ p > 0     := Iff.rfl
  _ ↔ sgn p ≃ 1 := gt_zero_sgn
  _ ↔ sgn p > 0 := sgn_gt_zero_iff_pos.symm

/--
A rational number is greater than or equivalent to zero iff its sign is greater
than or equivalent to zero.

**Property intuition**: Rationals greater than or equivalent to zero have sign
values of `1` and `0`, which are the only ones that are also greater than or
equivalent to zero.

**Proof intuition**: Split the _greater than or equivalent to_ relation into
_greater than_ or _equivalent to_. The theorem `sgn_preserves_gt_zero` covers
the _greater than_ relation, while `sgn_zero` covers _equivalent to_.
-/
theorem sgn_preserves_ge_zero {p : ℚ} : p ≥ 0 ↔ sgn p ≥ 0 := calc
  _ ↔ p ≥ 0                 := Iff.rfl
  _ ↔ p > 0 ∨ p ≃ 0         := ge_cases
  _ ↔ sgn p > 0 ∨ p ≃ 0     := iff_subst_covar or_mapL sgn_preserves_gt_zero
  _ ↔ sgn p > 0 ∨ sgn p ≃ 0 := iff_subst_covar or_mapR sgn_zero
  _ ↔ sgn p ≥ 0             := Integer.ge_split.symm

/--
A rational is greater than or equivalent to another exactly when the sign of
their difference is also greater than or equivalent to zero.

**Property and proof intuition**: The simpler property `p ≥ q ↔ p - q ≥ 0` is
already obvious using algebra. Add `sgn` on both sides and simplify.
-/
theorem ge_iff_sub_sgn_nonneg {p q : ℚ} : p ≥ q ↔ sgn (p - q) ≥ 0 := calc
  _ ↔ p ≥ q            := Rel.refl
  _ ↔ sgn (p - q) ≄ -1 := ge_sgn
  _ ↔ p - q ≥ 0        := ge_zero_sgn.symm
  _ ↔ sgn (p - q) ≥ 0  := sgn_preserves_ge_zero

/--
The _less than or equivalent to_ relation is decidable for rational numbers.

**Property and proof intuition**: The relation can be expressed as an
equivalence of integer sign values, which we already know to be decidable.
-/
instance le_decidable {p q : ℚ} : Decidable (p ≤ q) := by
  have : Decidable (sgn (p - q) ≃ 1) := Integer.eqv? (sgn (p - q)) 1
  match this with
  | isTrue (_ : sgn (p - q) ≃ 1) =>
    have : ¬(p ≤ q) := neg_le_sgn.mpr ‹sgn (p - q) ≃ 1›
    have : Decidable (p ≤ q) := isFalse this
    exact this
  | isFalse (_ : sgn (p - q) ≄ 1) =>
    have : p ≤ q := le_sgn.mpr ‹sgn (p - q) ≄ 1›
    have : Decidable (p ≤ q) := isTrue this
    exact this

/--
The _less than_ relation is decidable for rational numbers.

**Property and proof intuition**: The relation can be expressed as an
equivalence of integer sign values, which we already know to be decidable.
-/
instance lt_decidable {p q : ℚ} : Decidable (p < q) := by
  have : Decidable (sgn (p - q) ≃ -1) := Integer.eqv? (sgn (p - q)) (-1)
  match this with
  | isTrue (_ : sgn (p - q) ≃ -1) =>
    have : p < q := lt_sgn.mpr ‹sgn (p - q) ≃ -1›
    have : Decidable (p < q) := isTrue this
    exact this
  | isFalse (_ : sgn (p - q) ≄ -1) =>
    have : ¬(p < q) := mt lt_sgn.mp ‹sgn (p - q) ≄ -1›
    have : Decidable (p < q) := isFalse this
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
    sgn (p - r)             ≃ _ := by srw [←add_sub_telescope]
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
A _less than_ relation can be extended on the right by a _less than or
equivalent to_ relation through a common value.

**Property and proof intuition**: We know that the first value is less than the
second, so even if the second value is equivalent to the third, the first must
still be less than the third.
-/
theorem trans_lt_le_lt {p q r : ℚ} : p < q → q ≤ r → p < r := by
  intro (_ : p < q) (_ : q ≤ r)
  show p < r
  have : q < r ∨ q ≃ r := le_cases.mp ‹q ≤ r›
  match this with
  | Or.inl (_ : q < r) =>
    have : p < r := lt_trans ‹p < q› ‹q < r›
    exact this
  | Or.inr (_ : q ≃ r) =>
    have : p < r := by prw [‹q ≃ r›] ‹p < q›
    exact this

instance trans_lt_le_lt_inst : Trans (α := ℚ) (· < ·) (· ≤ ·) (· < ·) := {
  trans := trans_lt_le_lt
}

/--
A _less than_ relation can be extended on the left by a _less than or
equivalent to_ relation through a common value.

**Property and proof intuition**: We know that the second value is less than
the third, so even if the first value is equivalent to the second, the first
must still be less than the third.
-/
theorem trans_le_lt_lt {p q r : ℚ} : p ≤ q → q < r → p < r := by
  intro (_ : p ≤ q) (_ : q < r)
  show p < r
  have : p < q ∨ p ≃ q := le_cases.mp ‹p ≤ q›
  match this with
  | Or.inl (_ : p < q) =>
    have : p < r := lt_trans ‹p < q› ‹q < r›
    exact this
  | Or.inr (_ : p ≃ q) =>
    have : p < r := by prw [←‹p ≃ q›] ‹q < r›
    exact this

instance trans_le_lt_lt_inst : Trans (α := ℚ) (· ≤ ·) (· < ·) (· < ·) := {
  trans := trans_le_lt_lt
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
A _greater than_ relation can be extended on the right by a _greater than or
equivalent to_ relation through a common value.

**Property and proof intuition**: We know that the first value is greater than
the second, so even if the second value is equivalent to the third, the first
must still be greater than the third.
-/
theorem trans_gt_ge_gt {p q r : ℚ} : p > q → q ≥ r → p > r := by
  intro (_ : p > q) (_ : q ≥ r)
  show p > r
  have : q > r ∨ q ≃ r := ge_cases.mp ‹q ≥ r›
  match this with
  | Or.inl (_ : q > r) =>
    have : p > r := gt_trans ‹p > q› ‹q > r›
    exact this
  | Or.inr (_ : q ≃ r) =>
    have : r < p := by prw [‹q ≃ r›] ‹q < p›
    exact this

instance trans_gt_ge_gt_inst : Trans (α := ℚ) (· > ·) (· ≥ ·) (· > ·) := {
  trans := trans_gt_ge_gt
}

/--
A _greater than_ relation can be extended on the left by a _greater than or
equivalent to_ relation through a common value.

**Property and proof intuition**: We know that the second value is greater than
the third, so even if the first value is equivalent to the second, the first
must still be greater than the third.
-/
theorem trans_ge_gt_gt {p q r : ℚ} : p ≥ q → q > r → p > r := by
  intro (_ : p ≥ q) (_ : q > r)
  show p > r
  have : p > q ∨ p ≃ q := ge_cases.mp ‹p ≥ q›
  match this with
  | Or.inl (_ : p > q) =>
    have : p > r := gt_trans ‹p > q› ‹q > r›
    exact this
  | Or.inr (_ : p ≃ q) =>
    have : r < p := by prw [←‹p ≃ q›] ‹r < q›
    exact this

instance trans_ge_gt_gt_inst : Trans (α := ℚ) (· ≥ ·) (· > ·) (· > ·) := {
  trans := trans_ge_gt_gt
}

/--
Divide both operands of _less than_ by the same positive value.

**Property intuition**: Scaling two values by the same positive factor doesn't
change their relative ordering.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem lt_substN_div_pos
    {p q r : ℚ} (r_pos : sgn r ≃ 1)
    : have : AP (r ≄ 0) := AP.mk (nonzero_if_pos ‹sgn r ≃ 1›)
      p < q → p/r < q/r
    := by
  intro (_ : AP (r ≄ 0)) (_ : p < q)
  show p/r < q/r
  have : sgn (p/r - q/r) ≃ -1 := calc
    _ = sgn (p/r - q/r) := rfl
    _ ≃ sgn (p - q)     := sgn_sub_cancelR_div_pos ‹sgn r ≃ 1›
    _ ≃ -1              := lt_sgn.mp ‹p < q›
  have : p/r < q/r := lt_sgn.mpr ‹sgn (p/r - q/r) ≃ -1›
  exact this

/--
Divide both operands of _less than_ by the same negative value, reversing their
ordering.

**Property intuition**: Scaling two values by the same negative factor reflects
them across zero.

**Proof intuition**: Express the order relations in the hypothesis and the goal
via their `sgn`-based definitions. Show that they are equivalent using algebra
and substitution.
-/
theorem lt_substD_div_neg
    {p q r : ℚ} (r_neg : sgn r ≃ -1)
    : have : AP (r ≄ 0) := AP.mk (nonzero_if_neg ‹sgn r ≃ -1›)
      p < q → q/r < p/r
    := by
  intro (_ : AP (r ≄ 0)) (_ : p < q)
  show q/r < p/r
  have : sgn (q/r - p/r) ≃ -1 := calc
    _ = sgn (q/r - p/r) := rfl
    _ ≃ sgn (p - q)     := sgn_sub_cancelR_div_neg ‹sgn r ≃ -1›
    _ ≃ -1              := lt_sgn.mp ‹p < q›
  have : q/r < p/r := lt_sgn.mpr ‹sgn (q/r - p/r) ≃ -1›
  exact this

/--
The average of two nonequivalent rational numbers lies strictly between them.

**Property intuition**: Averaging finds the value that both numbers would have
if they were equal but with the same sum as the original numbers. Thus the
average must be bigger than the smaller number, and smaller than the bigger
number.

**Proof intuition**: Represent both numbers in units of one-half. Two halves of
`p` is less than one half of `p` and one half of `q`, by substitution on
`p < q`. Similarly, two halves of `q` is greater than the average value.
-/
theorem average
    {p q : ℚ}
    : have : AP ((2:ℚ) ≄ 0) := AP.mk (nonzero_if_pos sgn_two)
      p < q → p < (p + q)/2 ∧ (p + q)/2 < q
    := by
  intro (_ : AP ((2:ℚ) ≄ 0)) (_ : p < q)
  show p < (p + q)/2 ∧ (p + q)/2 < q
  have : p < (p + q)/2 := calc
    _ = p         := rfl
    _ ≃ (2 * p)/2 := eqv_symm mulL_div_same
    _ ≃ (p + p)/2 := by srw [mul_two_add]
    _ < (p + q)/2 := lt_substN_div_pos sgn_two (by srw [‹p < q›])
  have : (p + q)/2 < q := calc
    _ = (p + q)/2 := rfl
    _ < (q + q)/2 := lt_substN_div_pos sgn_two (by srw [‹p < q›])
    _ ≃ (2 * q)/2 := by srw [←mul_two_add]
    _ ≃ q         := mulL_div_same
  exact And.intro ‹p < (p + q)/2› ‹(p + q)/2 < q›

/--
The result of dividing a positive rational number by two lies strictly between
that number and zero.

**Proof intuition**: Follows directly from taking the average of zero and `p`.
-/
theorem halve
    {p : ℚ}
    : have : AP ((2:ℚ) ≄ 0) := AP.mk (nonzero_if_pos sgn_two)
      p > 0 → p > p/2 ∧ p/2 > 0
    := by
  intro (_ : AP ((2:ℚ) ≄ 0)) (_ : p > 0)
  show p > p/2 ∧ p/2 > 0
  have (And.intro (_ : 0 < (0 + p)/2) (_ : (0 + p)/2 < p)) := average ‹0 < p›
  have : p > p/2 := calc
    _ ≃ p         := eqv_refl
    _ > (0 + p)/2 := ‹(0 + p)/2 < p›
    _ ≃ p/2       := by srw [add_identL]
  have : p/2 > 0 := calc
    _ ≃ p/2       := eqv_refl
    _ ≃ (0 + p)/2 := by srw [←add_identL]
    _ > 0         := ‹0 < (0 + p)/2›
  exact And.intro ‹p > p/2› ‹p/2 > 0›

/--
The ordering of a nonnegative rational number and its negation.

**Property and proof intuition**: A nonnegative rational number is greater than
or equivalent to zero, so its negation must be less than or equivalent to zero.
Thus the result follows by transitivity.
-/
theorem le_neg_nonneg {p : ℚ} : p ≥ 0 → -p ≤ p := by
  intro (_ : p ≥ 0)
  show -p ≤ p
  have : -p ≤ 0 := calc
    _ ≃ -p := eqv_refl
    _ ≤ -0 := by srw [‹0 ≤ p›]
    _ ≃ 0  := neg_preserves_zero.mpr eqv_refl
  have : -p ≤ p := le_trans ‹-p ≤ 0› ‹0 ≤ p›
  exact this

/--
Provides evidence that the given rational number can be expressed as a ratio of
nonnegative integers.

Inductive types are the best option for existential statements, as their named
fields keep things organized, and they are allowed to inhabit `Prop`, unlike
structures.

**Why this is useful**: See `as_nonneg_ratio` below.
-/
inductive NonnegRatio (p : ℚ) : Prop where
| intro
    (a b : ℤ)
    (a_nneg : a ≥ 0)
    (b_pos : b > 0)
    (b_nz : AP ((b:ℚ) ≄ 0) :=
      have : (b:ℚ) > 0 := lt_respects_from_integer.mp ‹b > 0›
      have : (b:ℚ) ≄ 0 := pos_nonzero ‹(b:ℚ) > 0›
      AP.mk ‹(b:ℚ) ≄ 0›)
    (p_eqv : p ≃ a/b)
  : NonnegRatio p

/--
A nonnegative rational number can be expressed as a ratio of nonnegative
integers.

This is useful for simplifying proofs that convert rational numbers to integer
ratios: nonnegative integers can be easier to work with than general integers.

**Property intuition**: A nonnegative rational is either zero or positive. When
it's zero, it can be expressed as an integer ratio with a zero numerator. When
it's positive, it can be expressed either as a ratio of two positive integers,
or as a ratio of two negative integers. But in the negative case, the numerator
and denominator can both be multiplied by negative one to make them positive.
Thus, in all cases the numerator and denominator can always be nonnegative.

**Proof intuition**: Follows the strategy outlined in **Property intuition**,
but doesn't split into cases. Instead, explicitly defines the nonnegative
integers in the ratio as expressions involving `sgn`, and uses sign properties
to show that both must be nonnegative.
-/
theorem as_nonneg_ratio {p : ℚ} : p ≥ 0 → NonnegRatio p := by
  intro (_ : p ≥ 0)
  show NonnegRatio p
  have (AsRatio.mk (x : ℤ) (y : ℤ) (_ : AP (y ≄ 0)) p_eqv) := as_ratio p
  have : Integer.Nonzero y := Integer.nonzero_iff_neqv_zero.mpr ‹AP (y ≄ 0)›.ev
  have : p ≃ x/y := p_eqv
  let a := x * sgn y
  let b := y * sgn y

  have : sgn a ≥ 0 := calc
    _ = sgn a               := rfl
    _ = sgn (x * sgn y)     := rfl
    _ ≃ sgn x * sgn (sgn y) := Integer.sgn_compat_mul
    _ ≃ sgn x * sgn y       := by srw [Integer.sgn_idemp]
    _ ≃ sgn ((x:ℚ)/y)       := Rel.symm sgn_div_integers
    _ ≃ sgn p               := by srw [←‹p ≃ x/y›]
    _ ≥ 0                   := sgn_preserves_ge_zero.mp ‹p ≥ 0›
  have : a ≥ 0 := Integer.sgn_preserves_ge_zero.mpr ‹sgn a ≥ 0›

  have : Integer.Sqrt1 (sgn y) := Integer.sgn_nonzero.mp ‹Integer.Nonzero y›
  have : sgn b ≃ 1 := calc
    _ = sgn b               := rfl
    _ = sgn (y * sgn y)     := rfl
    _ ≃ sgn y * sgn (sgn y) := Integer.sgn_compat_mul
    _ ≃ sgn y * sgn y       := by srw [Integer.sgn_idemp]
    _ ≃ 1                   := ‹Integer.Sqrt1 (sgn y)›.elim
  have : b > 0 := Integer.gt_zero_sgn.mpr ‹sgn b ≃ 1›

  have : p ≃ a/b := calc
    _ = p                                   := rfl
    _ ≃ x/y                                 := ‹p ≃ x/y›
    _ ≃ ((x:ℚ)/y) * 1                       := eqv_symm mul_identR
    _ ≃ ((x:ℚ)/y) * (((sgn y:ℤ):ℚ)/(sgn y)) := by srw [←div_same]
    _ ≃ ((x:ℚ) * sgn y)/(y * sgn y)         := div_mul_swap
    _ ≃ ((x * sgn y : ℤ):ℚ)/(y * sgn y)     := by srw [←mul_compat_from_integer]
    _ = (a:ℚ)/(y * sgn y)                   := rfl
    _ ≃ (a:ℚ)/((y * sgn y : ℤ):ℚ)           := by srw [←mul_compat_from_integer]
    _ = (a:ℚ)/b                             := rfl

  have : NonnegRatio p := NonnegRatio.intro a b ‹a ≥ 0› ‹b > 0› _ ‹p ≃ a/b›
  exact this

end Lean4Axiomatic.Rational
