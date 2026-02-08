import Lean4Axiomatic.Integer.Parity

/-!
# Combined typeclass of all integer definitions and properties
-/

namespace Lean4Axiomatic

open Integer (
  Addition Core Division Induction Metric Multiplication Negation Order Parity
  Sign Subtraction
)

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
class Integer {ℕ : outParam Type} [Natural ℕ] (ℤ : Type) where
  toCore : Core (ℕ := ℕ) ℤ
  toAddition : Addition ℤ
  toMultiplication : Multiplication ℤ
  toExponentiation : Natural.Exponentiation ℕ ℤ
  toNegation : Negation ℤ
  toOrder : Order ℤ
  toSign : Sign ℤ
  toSubtraction : Subtraction ℤ
  toMetric : Metric ℤ
  toDivision : Division ℤ
  toParity : Parity ℤ
  toInduction₀ : Induction.{0} ℤ
  toInduction₁ : Induction.{1} ℤ

attribute [instance] Integer.toAddition
attribute [instance] Integer.toCore
attribute [instance] Integer.toDivision
attribute [instance] Integer.toExponentiation
attribute [instance] Integer.toInduction₀
attribute [instance] Integer.toInduction₁
attribute [instance] Integer.toMetric
attribute [instance] Integer.toMultiplication
attribute [instance] Integer.toNegation
attribute [instance] Integer.toOrder
attribute [instance] Integer.toParity
attribute [instance] Integer.toSign
attribute [instance] Integer.toSubtraction

namespace Signed

/--
Class providing the canonical name for the
[_signum_ function](https://en.wikipedia.org/wiki/Sign_function) on any type.
-/
class Sgn.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (α : Type)
    extends Integer.Sgn.Ops (ℤ := ℤ) α

export Integer.Sgn.Ops (sgn)

end Signed

end Lean4Axiomatic
