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

  /-- Multiplying by zero on the left always gives zero. -/
  zero_mul {m : ℕ} : 0 * m ≃ 0

  /--
  Take a product and increment the left-hand factor. This gives the same result
  as adding a copy of the right-hand factor to the original product.
  -/
  step_mul {n m : ℕ} : step n * m ≃ (n * m) + m

attribute [instance] Multiplication.Base.mulOp

/-- Properties that follow from those provided in `Multiplication.Base`. -/
class Multiplication.Derived (ℕ : Type) [Core ℕ] [Addition.Base ℕ]
    extends Multiplication.Base ℕ where
  /--
  Multiplication preserves equality of natural numbers; two equal natural
  numbers are still equal after the same quantity is multiplied with both (on
  the left or right).
  -/
  mul_substitutive : AA.Substitutive₂ (α := ℕ) (· * ·) (· ≃ ·) (· ≃ ·)

  /-- Multiplying by zero on the right always gives zero. -/
  mul_zero {n : ℕ} : n * 0 ≃ 0

  /--
  Take a product and increment the right-hand factor. This gives the same
  result as adding a copy of the left-hand factor to the original product.
  -/
  mul_step {n m : ℕ} : n * step m ≃ n * m + n

  /-- The order of the factors in a product doesn't matter. -/
  mul_commutative : AA.Commutative (α := ℕ) (· * ·)

namespace Multiplication
export Multiplication.Base (mulOp step_mul zero_mul)
export Multiplication.Derived (mul_commutative mul_substitutive)
end Multiplication

end Lean4Axiomatic.Natural
