import Lean4Axiomatic.Natural.Impl.Generic.Core
import Lean4Axiomatic.Natural.Impl.Generic.Exponentiation
import Lean4Axiomatic.Natural.Impl.Generic.Order
import Lean4Axiomatic.Natural.Impl.Generic.Sign

/-!
# Generic natural number axiom implementations

The term "generic" here means the implementations don't depend on the
implementation of the natural number type itself; i.e., they are generic, or
parameterized, over `ℕ`. Thus they can be used to provide part of a complete
implementation of `Natural`, no matter which concrete type is used for `ℕ`.
-/
