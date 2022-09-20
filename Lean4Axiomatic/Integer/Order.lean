import Lean4Axiomatic.Integer.Subtraction

/-! # Integer order -/

namespace Lean4Axiomatic.Integer

open Coe (coe)
open Signed (Negative Positive)

/-! ## Axioms -/

/-- Class defining the basic ordering relations on integers. -/
class Order (ℕ : Type) [Natural ℕ] (ℤ : Type) [Core ℕ ℤ] [Addition ℕ ℤ] :=
  /-- Definition of and syntax for the _less than or equal to_ relation. -/
  leOp : LE ℤ

  /--
  One integer is less than or equal to another iff adding a natural number to
  the lesser value produces the greater value.
  -/
  le_iff_add_nat {a b : ℤ} : a ≤ b ↔ ∃ k : ℕ, b ≃ a + coe k

  /-- Definition of and syntax for the _less than_ relation. -/
  ltOp : LT ℤ

  /-- The intuitive meaning of _less than_ in terms of _less than or equal_. -/
  lt_iff_le_neqv {a b : ℤ} : a < b ↔ a ≤ b ∧ a ≄ b

attribute [instance] Order.leOp
attribute [instance] Order.ltOp

export Order (le_iff_add_nat leOp lt_iff_le_neqv ltOp)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ] [Addition ℕ ℤ] [Multiplication ℕ ℤ]
variable [Negation ℕ ℤ] [Subtraction ℕ ℤ] [Sign ℕ ℤ] [Order ℕ ℤ]

/-! ## Derived properties -/

/--
Equivalence between the _greater than_ relation on integers and their
difference being positive.

**Property intuition**: For nonnegative values, this makes sense: taking away a
smaller value from a larger one should leave a positive amount behind. Taking
away a negative value is the same as adding its positive equivalent, which will
always give a positive result because the other number was "less negative".

**Proof intuition**: No special insight here; assumptions and goals are
expanded into their underlying properties, and then connected.
-/
theorem gt_iff_pos_diff {a b : ℤ} : a > b ↔ Positive (a - b) := by
  apply Iff.intro
  case mp =>
    intro (_ : b < a)
    show Positive (a - b)
    have (And.intro (_ : b ≤ a) (_ : b ≄ a)) := lt_iff_le_neqv.mp ‹b < a›
    have (Exists.intro (k : ℕ) (_ : a ≃ b + coe k)) :=
      le_iff_add_nat.mp ‹b ≤ a›
    have : a - b ≃ coe k := subR_move_addL.mpr ‹a ≃ b + coe k›
    have : a - b ≄ 0 := mt zero_diff_iff_eqv.mp (Rel.symm ‹b ≄ a›)
    have : coe k ≄ 0 := AA.substLFn (f := (· ≄ ·)) ‹a - b ≃ coe k› ‹a - b ≄ 0›
    have : k ≄ 0 := AA.inject ‹coe k ≄ coe (0 : ℕ)›
    have : Positive k := Signed.positive_defn.mpr ‹k ≄ 0›
    have : Positive (a - b) := positive_intro_nat ‹Positive k› ‹a - b ≃ coe k›
    exact this
  case mpr =>
    intro (_ : Positive (a - b))
    show b < a
    have
      (Exists.intro (k : ℕ) (And.intro (_ : Positive k) (_ : a - b ≃ coe k)))
        := positive_elim_nat ‹Positive (a - b)›
    apply lt_iff_le_neqv.mpr
    show b ≤ a ∧ b ≄ a
    have : a ≃ b + coe k := subR_move_addL.mp ‹a - b ≃ coe k›
    have : b ≤ a := le_iff_add_nat.mpr (Exists.intro k ‹a ≃ b + coe k›)
    have : k ≄ 0 := Signed.positive_defn.mp ‹Positive k›
    have : (coe k : ℤ) ≄ coe 0 := AA.subst₁ ‹k ≄ 0›
    have : a - b ≄ 0 :=
      AA.substLFn (f := (· ≄ ·)) (Rel.symm ‹a - b ≃ coe k›) ‹(coe k : ℤ) ≄ 0›
    have : b ≄ a := Rel.symm (mt zero_diff_iff_eqv.mpr ‹a - b ≄ 0›)
    exact And.intro ‹b ≤ a› ‹b ≄ a›

/--
Equivalent integers can be substituted on the left of the `· ≤ ·` relation.

**Property intuition**: This must be true for `· ≤ ·` to be a valid integer
relation.

**Proof intuition**: The result follows from transitivity and substitution on
the underlying definition of `· ≤ ·`.
-/
theorem le_substL_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ ≤ b → a₂ ≤ b := by
  intro (_ : a₁ ≃ a₂) (_ : a₁ ≤ b)
  show a₂ ≤ b
  have (Exists.intro (k : ℕ) (_ : b ≃ a₁ + coe k)) :=
    le_iff_add_nat.mp ‹a₁ ≤ b›
  apply le_iff_add_nat.mpr
  show ∃ (k : ℕ), b ≃ a₂ + coe k
  have : b ≃ a₂ + coe k := Rel.trans ‹b ≃ a₁ + coe k› (AA.substL ‹a₁ ≃ a₂›)
  exact Exists.intro k ‹b ≃ a₂ + coe k›

/--
Equivalent integers can be substituted on the right of the `· ≤ ·` relation.

**Property intuition**: This must be true for `· ≤ ·` to be a valid integer
relation.

**Proof intuition**: The result follows from transitivity and substitution on
the underlying definition of `· ≤ ·`.
-/
theorem le_substR_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b ≤ a₁ → b ≤ a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : b ≤ a₁)
  show b ≤ a₂
  have (Exists.intro (k : ℕ) (_ : a₁ ≃ b + coe k)) :=
    le_iff_add_nat.mp ‹b ≤ a₁›
  apply le_iff_add_nat.mpr
  show ∃ (k : ℕ), a₂ ≃ b + coe k
  have : a₂ ≃ b + coe k := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ b + coe k›
  exact Exists.intro k ‹a₂ ≃ b + coe k›

instance le_substitutive_eqv
    : AA.Substitutive₂ (α := ℤ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => le_substL_eqv }
  substitutiveR := { subst₂ := λ (_ : True) => le_substR_eqv }
}

/--
Equivalent integers can be substituted on the left of the `· < ·` relation.

**Property intuition**: This must be true for `· < ·` to be a valid integer
relation.

**Proof intuition**: The result follows from substitution on the underlying
definition of `· < ·`.
-/
theorem lt_substL_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ < b → a₂ < b := by
  intro (_ : a₁ ≃ a₂) (_ : a₁ < b)
  show a₂ < b
  have (And.intro (_ : a₁ ≤ b) (_ : a₁ ≄ b)) := lt_iff_le_neqv.mp ‹a₁ < b›
  apply lt_iff_le_neqv.mpr
  show a₂ ≤ b ∧ a₂ ≄ b
  have : a₂ ≤ b := AA.substLFn ‹a₁ ≃ a₂› ‹a₁ ≤ b›
  have : a₂ ≄ b := AA.substLFn (f := (· ≄ ·)) ‹a₁ ≃ a₂› ‹a₁ ≄ b›
  exact And.intro ‹a₂ ≤ b› ‹a₂ ≄ b›

/--
Equivalent integers can be substituted on the right of the `· < ·` relation.

**Property intuition**: This must be true for `· < ·` to be a valid integer
relation.

**Proof intuition**: The result follows from substitution on the underlying
definition of `· < ·`.
-/
theorem lt_substR_eqv {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b < a₁ → b < a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : b < a₁)
  show b < a₂
  have (And.intro (_ : b ≤ a₁) (_ : b ≄ a₁)) := lt_iff_le_neqv.mp ‹b < a₁›
  apply lt_iff_le_neqv.mpr
  show b ≤ a₂ ∧ b ≄ a₂
  have : b ≤ a₂ := AA.substRFn ‹a₁ ≃ a₂› ‹b ≤ a₁›
  have : b ≄ a₂ := AA.substRFn (f := (· ≄ ·)) ‹a₁ ≃ a₂› ‹b ≄ a₁›
  exact And.intro ‹b ≤ a₂› ‹b ≄ a₂›

instance lt_substitutive_eqv
    : AA.Substitutive₂ (α := ℤ) (· < ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => lt_substL_eqv }
  substitutiveR := { subst₂ := λ (_ : True) => lt_substR_eqv }
}

/--
The `· < ·` relation is preserved when the same value is added on the right to
both sides.

**Property intuition**: Both values are changed by the same amount, so their
ordering won't be affected.

**Proof intuition**: Convert the `· < ·` relation into subtraction; then the
common value gets canceled out.
-/
theorem add_substL_lt {a b c : ℤ} : a < b → a + c < b + c := by
  intro (_ : a < b)
  show a + c < b + c
  have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
  apply gt_iff_pos_diff.mpr
  show Positive (b + c - (a + c))
  have : b - a ≃ b + c - (a + c) := Rel.symm sub_sums_sameR
  exact AA.substFn ‹b - a ≃ b + c - (a + c)› ‹Positive (b - a)›

def add_substitutiveL_lt
    : AA.SubstitutiveOn Hand.L (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  subst₂ := λ (_ : True) => add_substL_lt
}

instance add_substitutive_lt
    : AA.Substitutive₂ (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  substitutiveL :=
    add_substitutiveL_lt
  substitutiveR :=
    AA.substR_from_substL_swap (rS := (· ≃ ·)) add_substitutiveL_lt
}

/--
The `· < ·` relation on sums with the same left operand is preserved when that
operand is removed from both.

**Property intuition**: Both remaining values had been changed by the same
amount due to the sums, so their ordering won't be affected.

**Proof intuition**: Convert the `· < ·` relation into subtraction; then the
common value gets canceled out.
-/
theorem add_cancelL_lt {a b c : ℤ} : c + a < c + b → a < b := by
  intro (_ : c + a < c + b)
  show a < b
  have : Positive (c + b - (c + a)) := gt_iff_pos_diff.mp ‹c + a < c + b›
  apply gt_iff_pos_diff.mpr
  show Positive (b - a)
  have : c + b - (c + a) ≃ b - a := calc
    c + b - (c + a) ≃ _ := AA.substL AA.comm
    b + c - (c + a) ≃ _ := AA.substR AA.comm
    b + c - (a + c) ≃ _ := sub_sums_sameR
    b - a ≃ _ := Rel.refl
  apply AA.substFn ‹c + b - (c + a) ≃ b - a›
  exact ‹Positive (c + b - (c + a))›

def add_cancellativeL_lt
    : AA.CancellativeOn Hand.L (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  cancel := λ (_ : True) => add_cancelL_lt
}

instance add_cancellative_lt
    : AA.Cancellative (α := ℤ) (· + ·) AA.tc (· < ·) (· < ·)
    := {
  cancellativeL := add_cancellativeL_lt
  cancellativeR := AA.cancelR_from_cancelL add_cancellativeL_lt
}

/--
The `· < ·` relation is preserved when both sides are multiplied on the right
by the same positive value.

**Property intuition**: Both values are scaled away from zero by the same
factor, so their ordering won't be affected; positive values become more
positive and negative values become more negative.

**Proof intuition**: The goal `a * c < b * c` can be expressed as
`Positive (b * c - a * c)`, which factors into `Positive ((b - a) * c)`. The
result follows by showing that the two factors being positive means that their
product is positive.
-/
theorem mul_substL_lt {a b c : ℤ} : Positive c → a < b → a * c < b * c := by
  intro (_ : Positive c) (_ : a < b)
  show a * c < b * c
  have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
  apply gt_iff_pos_diff.mpr
  show Positive (b * c - a * c)
  apply AA.substFn AA.distribR
  show Positive ((b - a) * c)
  exact mul_preserves_positive ‹Positive (b - a)› ‹Positive c›

def mul_substitutiveL_lt
    : AA.SubstitutiveOn Hand.L (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  subst₂ := mul_substL_lt
}

instance mul_substitutive_lt
    : AA.Substitutive₂ (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  substitutiveL :=
    mul_substitutiveL_lt
  substitutiveR :=
    AA.substR_from_substL_swap (rS := (· ≃ ·)) mul_substitutiveL_lt
}

/--
The `· < ·` relation on products with the same (positive) left factor is
preserved when that factor is removed from both products.

**Property intuition**: Both values are scaled towards zero by the same factor,
so their ordering won't be affected; positive values become less positive and
negative values become less negative.

**Proof intuition**: The assumption `c * a < c * b` can be expressed as
`Positive (c * b - c * a)`, which factors into `Positive (c * (b - a))`. Thus
`c` and `b - a` must have the same sign, and since `c` is positive, `b - a` is
as well, giving the result.
-/
theorem mul_cancelL_lt {a b c : ℤ} : Positive c → c * a < c * b → a < b := by
  intro (_ : Positive c) (_ : c * a < c * b)
  show a < b
  have : Positive (c * b - c * a) := gt_iff_pos_diff.mp ‹c * a < c * b›
  apply gt_iff_pos_diff.mpr
  show Positive (b - a)
  have : Positive (c * (b - a)) :=
    AA.substFn (Rel.symm AA.distribL) ‹Positive (c * b - c * a)›
  have : SameSign c (b - a) :=
    positive_mul_iff_same_sign.mp ‹Positive (c * (b - a))›
  have : Positive (b - a) :=
    same_sign_positive ‹SameSign c (b - a)› ‹Positive c›
  exact this

def mul_cancellativeL_lt
    : AA.CancellativeOn Hand.L (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  cancel := mul_cancelL_lt
}

instance mul_cancellative_lt
    : AA.Cancellative (α := ℤ) (· * ·) Positive (· < ·) (· < ·)
    := {
  cancellativeL := mul_cancellativeL_lt
  cancellativeR := AA.cancelR_from_cancelL mul_cancellativeL_lt
}

/--
Negation reverses order.

**Property intuition**: The sequence of negative integers, in the standard
order, is backwards compared to the positive integers: counting upwards,
negative integers reduce in magnitude (get closer to zero) while positive
integers increase in magnitude (get farther from zero).

**Proof intuition**: Expanding the definition of ordering into a property about
positive integers, the proof just requires showing that two integer expressions
are the same.
-/
theorem lt_neg_flip {a b : ℤ} : a < b ↔ -b < -a := by
  have : -a - -b ≃ b - a := calc
    (-a) - -b    ≃ _ := sub_defn
    (-a) + -(-b) ≃ _ := AA.substR neg_involutive
    (-a) + b     ≃ _ := AA.comm
    b + -a       ≃ _ := Rel.symm sub_defn
    b - a        ≃ _ := Rel.refl
  apply Iff.intro
  case mp =>
    intro (_ : a < b)
    show -b < -a
    have : Positive (b - a) := gt_iff_pos_diff.mp ‹a < b›
    apply gt_iff_pos_diff.mpr
    show Positive (-a - -b)
    exact AA.substFn (Rel.symm ‹-a - -b ≃ b - a›) ‹Positive (b - a)›
  case mpr =>
    intro (_ : -b < -a)
    show a < b
    have : Positive (-a - -b) := gt_iff_pos_diff.mp ‹-b < -a›
    apply gt_iff_pos_diff.mpr
    show Positive (b - a)
    exact AA.substFn ‹-a - -b ≃ b - a› ‹Positive (-a - -b)›

instance lt_substitutive_neg
    : AA.Substitutive₁ (α := ℤ) (-·) (· < ·) (· > ·)
    := {
  subst₁ := lt_neg_flip.mp
}

instance lt_injective_neg : AA.Injective (α := ℤ) (-·) (· < ·) (· > ·) := {
  inject := lt_neg_flip.mpr
}

end Lean4Axiomatic.Integer
