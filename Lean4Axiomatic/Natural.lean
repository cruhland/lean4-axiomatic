import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators

import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.Natural.Sign

open Operators (TildeDash)

namespace ℕ

class Decl (ℕ : Type) where
  [toAddition : Addition ℕ]
  [toSignProperties : SignProperties ℕ]
  [toOrderProperties : OrderProperties ℕ]

attribute [instance] Decl.toAddition
attribute [instance] Decl.toSignProperties
attribute [instance] Decl.toOrderProperties

end ℕ
