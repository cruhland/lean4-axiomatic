import Lean4Axiomatic.AbstractAlgebra.Substitutive

namespace Lean4Axiomatic.CA.Monoid

open Relation.Equivalence (EqvOp)

/-!
An attempt at formalizing traditional algebraic structures
such as groups and rings.

Here we introduce a Monoid using a multiplicative notation.

Note that we only require a binary operation that is associative and
has identities.  For example, the natural numbers with the addition
operator is a monoid.
-/

/-! ### Definitions -/

/--
Operations for Monoid, namely the binary operation and identity element.
-/
class Ops (α : Type) :=
  binop : α → α → α
  ident : α
export Ops (ident)

/-- Enables the use of the `· * ·` operator for f (the monoid operation). -/
local instance monoid_mul_op_inst {α : Type} [Monoid.Ops α] : Mul α := {
  mul := Monoid.Ops.binop
}

/-- Properties of Monoid. -/
class Props (α : Type) [EqvOp α] [Ops α] :=
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identL {x : α} : ident * x ≃ x
  identR {x : α} : x * ident ≃ x
export Props (substL substR assoc identL identR)

class Monoid (α : Type) [EqvOp α] :=
  toOps : Monoid.Ops α
  toProps : Monoid.Props α

attribute [instance] Monoid.toOps
attribute [instance] Monoid.toProps


/-! ### Properties -/

variable {α : Type} [EqvOp α] [m : Monoid α]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
instance monoid_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

/--
Intuition: There is only one element, namely the identity ident, such that
  ident * y ≃ ident for all elements y.

Technical note: when we say one element, we don't mean uniqueness in the
underlying type α, as α could use a representation where many elements
are equivalent to ident under the ≃ relation. For example, α could a type
representing rational numbers as ratios of integers where
ident = 0 / 0 = 0 / 1, etc...

What we show is that elements x satisfying the x_is_left_ident are equivalent
to ident.
More formally, the quotient class α/≃ has only one element whose members
satisfy the identity condition.

From the perspective of the monoid and matching intuition, all elements that
are equivalent are treated the same.
-/
theorem mul_identity_unique
    {x : α} (x_is_left_ident : ((y : α) → (x * y) ≃ y)) : x ≃ ident := calc
  _ = x     := rfl
  _ ≃ x * ident := Rel.symm identR
  _ ≃ ident     := x_is_left_ident ident
