import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators

import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.Natural.Sign

open Operators (TildeDash)

namespace Lean4Axiomatic
namespace Natural

class Decl (ℕ : Type) where
  [toCore : Core ℕ]
  [toAddition : Addition.Derived ℕ]
  [toSign : Sign.Derived ℕ]
  [toOrder : Order.Derived ℕ]

end Natural
end Lean4Axiomatic
