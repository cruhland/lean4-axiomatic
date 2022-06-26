
namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer subtraction
-/

/--
Definition of subtraction, and properties that it must satisfy.

All other properties of subtraction can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.
-/
class Subtraction.Base (ℤ : Type) :=
  /-- Definition of and syntax for subtraction. -/
  subOp : Sub ℤ

end Lean4Axiomatic.Integer
