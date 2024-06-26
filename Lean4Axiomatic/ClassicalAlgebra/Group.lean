import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA.Group

open Relation.Equivalence (EqvOp)


/-!
A formalization of Group using multiplicative notation.
-/

/-! ### Definitions -/

/--
Operations for Group, namely the binary operation, identity element, and
existence of inverses.
-/
class Ops (α : Type) :=
  binop : α → α → α
  ident : α
  inverse : (x : α) → α

export Ops (ident inverse)

/-- Enables the use of the `· * ·` operator for f (the monoid operation). -/
local instance group_mul_op_inst {α : Type} [Ops α] : Mul α := {
  mul := Group.Ops.binop
}

/-- Properties of Group. -/
class Props (α : Type) [EqvOp α] [Ops α] :=
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identL {x : α} : ident * x ≃ x
  identR {x : α} : x * ident ≃ x
  inverse_propL (x : α) : (inverse x) * x ≃ ident
  inverse_propR (x : α) : x * (inverse x) ≃ ident

export Props (
  substL substR assoc identL identR inverse_propL inverse_propR
)

/-- All axioms for generic types to form a Group. -/
class Group (α : Type) [EqvOp α] :=
  toOps : Group.Ops α
  toProps : Group.Props α

attribute [instance] Group.toOps
attribute [instance] Group.toProps

/-! ### Properties -/

variable {α : Type} [EqvOp α] [g : Group α]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
instance group_subst_inst
    : AA.Substitutive₂ (α := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

/--
You May perform cancellation of an element x, and conclude from
x * y ≃ x * z that y ≃ z.
-/
def group_cancellationL
    {x y z : α} : (x * y ≃ x * z) → y ≃ z := λ _ =>
  show y ≃ z from calc
    _ ≃ y                     := Rel.refl
    _ ≃ ident * y             := Rel.symm identL
    _ ≃ ((inverse x) * x) * y := substL (Rel.symm (inverse_propL x))
    _ ≃ (inverse x) * (x * y) := assoc
    _ ≃ (inverse x) * (x * z) := substR ‹x * y ≃ x * z›
    _ ≃ (inverse x * x) * z   := Rel.symm assoc
    _ ≃ ident * z             := substL (inverse_propL x)
    _ ≃ z                     := identL


local instance monoid_from_group_ops :  CA.Monoid.Ops α := {
  binop := (· * ·)
  ident := g.toOps.ident
}

/--
Demonstrates that any group is also a monoid.
-/
instance monoid_from_group : CA.Monoid.Monoid (α := α) := {
  toOps := monoid_from_group_ops
  toProps := {
    substL    := g.toProps.substL
    substR    := g.toProps.substR
    assoc     := g.toProps.assoc
    identL := g.toProps.identL
    identR := g.toProps.identR
  }
}

/--
  There is only one element, namely the identity ident, such that
  ident * y ≃ ident for all elements y.  The proof follows from the fact that
  Groups are Monoids and the result holds for Monoids.
-/
theorem mul_identity_unique
    {x : α} (x_is_left_ident : ((y : α) → (x * y) ≃ y)) : x ≃ ident :=
  Lean4Axiomatic.CA.Monoid.mul_identity_unique x_is_left_ident
