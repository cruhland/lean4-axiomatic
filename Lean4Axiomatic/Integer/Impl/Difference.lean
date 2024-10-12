import Lean4Axiomatic.Integer.Impl.Difference.Induction
import Lean4Axiomatic.Integer.Impl.Difference.Sign
import Lean4Axiomatic.Integer.Impl.Generic.Order
import Lean4Axiomatic.Natural.Impl.Generic.Exponentiation

/-! # Implementation of integers as formal differences of natural numbers -/

namespace Lean4Axiomatic.Integer.Impl.Difference

variable {ℕ : Type} [Natural ℕ] [Natural.Induction.{1} ℕ]

instance integer : Integer (ℕ := ℕ) (Difference ℕ) := {
  toAddition := addition
  toCore := core
  toExponentiation := Natural.Impl.Generic.exponentiation
  toInduction := induction
  toMultiplication := multiplication
  toNegation := negation
  toOrder := Generic.order
  toSign := sign
  toSubtraction := Generic.subtraction
}

end Lean4Axiomatic.Integer.Impl.Difference
