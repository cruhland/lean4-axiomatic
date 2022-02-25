import Lean4Axiomatic.Natural.Addition

namespace Lean4Axiomatic.Natural

/-!
# Definition and properties of natural number multiplication
-/

/--
Definition of multiplication, and properties that it must satisfy.

All other properties of multiplication can be derived from these.
-/
class Multiplication.Base (ℕ : Type) [Core ℕ] [Addition.Base ℕ] where
  /-- Definition of and syntax for multiplication. -/
  mulOp : Mul ℕ

  /-- Zero times anything is zero (i.e., zero is an absorbing element). -/
  zero_mul {m : ℕ} : 0 * m ≃ 0

  /-- Incrementing the left factor adds the right factor to their product. -/
  step_mul {n m : ℕ} : step n * m ≃ (n * m) + m

namespace Multiplication
export Multiplication.Base (mulOp step_mul zero_mul)
end Multiplication

export Multiplication (mulOp step_mul zero_mul)

end Lean4Axiomatic.Natural
