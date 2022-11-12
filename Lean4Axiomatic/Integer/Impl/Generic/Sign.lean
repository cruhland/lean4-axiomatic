import Lean4Axiomatic.Integer.Sign

/-! # Generic implementations of integer signedness properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ]
variable [Addition ℕ ℤ] [Multiplication ℕ ℤ] [Negation ℕ ℤ]

open Signed (Negative Positive)

/--
Definitions of signedness predicates on integers.

These definitions are generic in that they don't depend on the underlying
implementation of the integers (the type `ℤ`). This allows them to be used by
any integer implementation directly.

These definitions are in a separate `Ops` class so that subsequent results in
this file can use the canonical predicate names.
-/
instance signed_ops : Signed.Ops ℤ := {
  Positive := λ (a : ℤ) => NonzeroWithSign a 1
  Negative := λ (a : ℤ) => NonzeroWithSign a (-1)
  Nonzero := Nonzero
}

/--
An integer is positive iff it has sign `1` in signed-magnitude form.

**Property intuition**: Integers in signed-magnitude form are the product of an
integer sign and a positive natural number magnitude. Multiplying a positive
natural number by the integer `1` should produce a positive integer.

**Proof intuition**: Trivial because `Positive` is defined as this property.
-/
theorem positive_iff_sign_pos1 {a : ℤ} : Positive a ↔ NonzeroWithSign a 1 :=
  Iff.intro id id

/--
An integer is negative iff it has sign `-1` in signed-magnitude form.

**Property intuition**: Integers in signed-magnitude form are the product of an
integer sign and a positive natural number magnitude. Multiplying a positive
natural number by the integer `-1` should produce a negative integer.

**Proof intuition**: Trivial because `Negative` is defined as this property.
-/
theorem negative_iff_sign_neg1 {a : ℤ} : Negative a ↔ NonzeroWithSign a (-1) :=
  Iff.intro id id

/--
The `Signed.Nonzero` predicate is equivalent to the `Integer.Nonzero` class.

**Intuition**: Defined to be the case in `signed_ops`.
-/
theorem nonzero_iff_nonzero_impl
    {a : ℤ} : Signed.Nonzero a ↔ Integer.Nonzero a
    :=
  Iff.intro id id

end Lean4Axiomatic.Integer.Impl.Generic
