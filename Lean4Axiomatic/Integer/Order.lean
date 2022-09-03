import Lean4Axiomatic.Integer.Subtraction

/-! # Integer order -/

namespace Lean4Axiomatic.Integer

open Coe (coe)
open Signed (Positive)

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

end Lean4Axiomatic.Integer
