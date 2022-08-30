import Lean4Axiomatic.Integer.Addition

/-! # Integer order -/

namespace Lean4Axiomatic.Integer

open Coe (coe)

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

end Lean4Axiomatic.Integer
