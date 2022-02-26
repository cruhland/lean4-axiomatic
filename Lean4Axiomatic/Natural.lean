import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators

import Lean4Axiomatic.Natural.Multiplication
import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic.Natural

open Operators (TildeDash)

class Decl (ℕ : Type) where
  toCore : Core ℕ
  toAddition : Addition.Derived ℕ
  toSign : Sign.Derived ℕ
  toOrder : Order.Derived ℕ
  toMultiplication : Multiplication.Derived ℕ

export Multiplication (
  mul_commutative mulOp mul_substitutive step_mul zero_mul
)
export Sign (Positive positive_add positive_defn positive_step)

end Lean4Axiomatic.Natural
