import Lean4Axiomatic.Natural.Addition
import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic.Natural

open Signed (Positive)

/-!
# Definition and properties of natural number order
-/

/--
Definition of the _less than or equal to_ and _less than_ relations.

All other properties of ordering on natural numbers can be derived from this.
-/
class Order.Base (ℕ : Type) [Core ℕ] [Addition.Base ℕ] :=
  /-- Definition of and syntax for the _less than or equal to_ relation. -/
  leOp : LE ℕ

  /--
  The _less than or equal to_ relation between two natural numbers `n` and `m`
  is equivalent to there being a natural number -- the _difference_ between `n`
  and `m` -- that, when added to `n`, results in `m`.
  -/
  le_defn {n m : ℕ} : n ≤ m ↔ ∃ k : ℕ, n + k ≃ m

  /-- Definition of and syntax for the _less than_ relation. -/
  ltOp : LT ℕ

  /--
  The _less than_ relation between two natural numbers is defined to be the
  same as _less than or equal to_, with the added condition that the numbers
  are not equal.
  -/
  lt_defn {n m : ℕ} : n < m ↔ n ≤ m ∧ n ≄ m

-- Higher priority than the stdlib definitions
attribute [instance default+1] Order.Base.leOp
attribute [instance default+1] Order.Base.ltOp

/-- Properties that follow from those provided in `Order.Base`. -/
class Order.Derived
    (ℕ : Type) [Core ℕ] [Addition.Base ℕ] [Sign.Base ℕ]
    extends Order.Base ℕ
    :=
  /--
  The _less than or equal to_ relation is preserved when both sides are
  incremented.
  -/
  le_substitutive_step : AA.Substitutive₁ (α := ℕ) step (· ≤ ·) (· ≤ ·)

  /--
  The _less than or equal to_ relation is preserved when both sides are
  decremented.
  -/
  le_injective_step : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·)

  /--
  Equal natural numbers can be substituted on either side of
  _less than or equal to_.
  -/
  le_substitutive_eqv : AA.Substitutive₂ (α := ℕ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)

  /-- All natural numbers are _less than or equal to_ themselves. -/
  le_reflexive : Relation.Reflexive (α := ℕ) (· ≤ ·)

  /--
  The _less than or equal to_ relation can be extended through intermediate
  values.
  -/
  le_transitive : Relation.Transitive (α := ℕ) (· ≤ ·)

  /-- Two natural numbers `n` and `m` are equal if `n ≤ m` and `m ≤ n`. -/
  le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m

  /--
  The _less than or equal to_ relation is preserved when the same value is
  added to both sides.
  -/
  le_substitutive_add : AA.Substitutive₂ (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)

  /--
  The _less than or equal to_ relation is preserved when the same value is
  removed from an addition on both sides.
  -/
  le_cancellative_add : AA.Cancellative (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)

  /-- Weakens equality to _less than or equal to_. -/
  le_from_eqv {n m : ℕ} : n ≃ m → n ≤ m

  /-- Weakens _less than_ to _less than or equal to_. -/
  le_from_lt {n m : ℕ} : n < m → n ≤ m

  /--
  As the name implies, if _less than or equal to_ holds between two natural
  numbers, then either _less than_ holds between them as well, or the numbers
  are equal.
  -/
  le_split {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m

  /--
  Equal natural numbers can be substituted on either side of _less than_.
  -/
  lt_substitutive_eqv : AA.Substitutive₂ (α := ℕ) (· < ·) AA.tc (· ≃ ·) (· → ·)

  /-- The _less than_ relation can be extended through intermediate values. -/
  lt_transitive : Relation.Transitive (α := ℕ) (· < ·)

  /-- No natural number is less than zero. -/
  lt_zero {n : ℕ} : n ≮ 0

  /-- A natural number is positive iff it's greater than zero. -/
  lt_zero_pos {n : ℕ} : Positive n ↔ n > 0

  /-- A natural number is always less than its successor. -/
  lt_step {n : ℕ} : n < step n

  /--
  A useful way to convert between _less than_ and _less than or equal to_ while
  keeping the larger number fixed.
  -/
  lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m

  /--
  The _less than_ relation between two natural numbers `n` and `m` is
  equivalent to there being a positive natural number -- the _difference_
  between `n` and `m` -- that, when added to `n`, results in `m`.
  -/
  lt_defn_add {n m : ℕ} : n < m ↔ ∃ k, Positive k ∧ m ≃ n + k

  /--
  Useful result when needing to decrement the larger number in a _less than_
  relation.
  -/
  lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m

  /--
  Very general property about ordering which often simplifies proofs that would
  otherwise have had to use induction.
  -/
  trichotomy (n m : ℕ) : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m)

attribute [instance] Order.Derived.le_substitutive_eqv
attribute [instance] Order.Derived.lt_substitutive_eqv
attribute [instance] Order.Derived.lt_transitive

namespace Order
export Order.Base (le_defn leOp lt_defn ltOp)
export Order.Derived (
  le_antisymm le_reflexive le_split le_transitive
  lt_defn_add lt_split lt_step lt_step_le lt_transitive lt_zero lt_zero_pos
  trichotomy
)
end Order

end Lean4Axiomatic.Natural
