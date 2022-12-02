import Lean4Axiomatic.Integer.Order
import Lean4Axiomatic.Integer.Subtraction

/-!
# Combined typeclass of all integer definitions and properties
-/

namespace Lean4Axiomatic

open Integer (Addition Core Multiplication Negation Order Sign Subtraction)

/--
The class of [integers](https://en.wikipedia.org/wiki/Integer).

It is parameterized not only on a type `ℤ` that must satisfy the properties of
integers, but also on a type `ℕ` that obeys the properties of natural numbers
(via `Natural ℕ`). This is to support the crucial fact that a bijection exists
between the natural numbers and the nonnegative integers (provided by
`Integer.Conversion.from_natural`).

Although there are many integer properties expressed by this class, most of
them can be derived from a few essential ones, reducing the work required to
construct an instance.

**Named parameters**
- `ℕ`: A type that obeys all of the properties of the natural numbers.
- `ℤ`: A type that obeys all of the properties provided by this class.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
-/
class Integer {ℕ : outParam Type} [outParam (Natural ℕ)] (ℤ : Type) :=
  toCore : Core (ℕ := ℕ) ℤ
  toAddition : Addition ℤ
  toMultiplication : Multiplication ℤ
  toNegation : Negation ℤ
  toOrder : Order ℤ
  toSign : Sign ℤ
  toSubtraction : Subtraction ℤ

attribute [instance] Integer.toAddition
attribute [instance] Integer.toCore
attribute [instance] Integer.toMultiplication
attribute [instance] Integer.toNegation
attribute [instance] Integer.toOrder
attribute [instance] Integer.toSign
attribute [instance] Integer.toSubtraction

end Lean4Axiomatic
