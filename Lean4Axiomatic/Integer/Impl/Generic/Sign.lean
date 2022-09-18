import Lean4Axiomatic.Integer.Sign

/-! # Generic implementations of integer signedness properties -/

namespace Lean4Axiomatic.Integer.Impl.Generic

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ]
variable [Addition ℕ ℤ] [Multiplication ℕ ℤ] [Negation ℕ ℤ]

open Signed (Negative Positive)

/--
Definitions of the `Positive` and `Negative` predicates on integers.

These definitions are generic in that they don't depend on the underlying
implementation of the integers (the type `ℤ`). This allows them to be used by
any integer implementation directly.

These definitions are in a separate `Ops` class so that subsequent results in
this file can use the canonical `Positive` and `Negative` predicates.
-/
instance signed_ops : Signed.Ops ℤ := {
  Positive := λ (a : ℤ) => NonzeroWithSign a 1
  Negative := λ (a : ℤ) => NonzeroWithSign a (-1)
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
The `Positive` predicate respects equivalence.

**Property intuition**: This must be true for `Positive` to make sense as a
predicate.

**Proof intuition**: The definition of `Positive` is an equivalence between the
integer argument of the predicate and an expression. Since we also have an
equivalence for substitution, the result follows by transitivity.
-/
theorem positive_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → Positive a₁ → Positive a₂ := by
  intro (_ : a₁ ≃ a₂)
  intro (NonzeroWithSign.intro (m : ℕ) (_ : Positive m) (_ : a₁ ≃ 1 * ↑m))
  show NonzeroWithSign a₂ 1
  have : a₂ ≃ 1 * ↑m := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ 1 * ↑m›
  exact NonzeroWithSign.intro m ‹Positive m› ‹a₂ ≃ 1 * ↑m›

def positive_substitutive
    : AA.Substitutive₁ (α := ℤ) Positive (· ≃ ·) (· → ·)
    := {
  subst₁ := positive_subst
}

/--
The `Negative` predicate respects equivalence.

**Property intuition**: This must be true for `Negative` to make sense as a
predicate.

**Proof intuition**: The definition of `Negative` is an equivalence between the
integer argument of the predicate and an expression. Since we also have an
equivalence for substitution, the result follows by transitivity.
-/
theorem negative_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → Negative a₁ → Negative a₂ := by
  intro (_ : a₁ ≃ a₂)
  intro (NonzeroWithSign.intro (m : ℕ) (_ : Positive m) (_ : a₁ ≃ -1 * ↑m))
  show NonzeroWithSign a₂ (-1)
  have : a₂ ≃ -1 * ↑m := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ -1 * ↑m›
  exact NonzeroWithSign.intro m ‹Positive m› ‹a₂ ≃ -1 * ↑m›

def negative_substitutive
    : AA.Substitutive₁ (α := ℤ) Negative (· ≃ ·) (· → ·)
    := {
  subst₁ := negative_subst
}

end Lean4Axiomatic.Integer.Impl.Generic
