import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.Monoid

namespace Lean4Axiomatic.CA

open Relation.Equivalence (EqvOp)
/-!
A formalization of Group using multiplicative notation.
-/

/-! ### Definitions -/

class Group.Ops (α : Type) [EqvOp α] where
  f : α → α → α
  e : α

export Group.Ops (f e)

/-- Enables the use of the `· * ·` operator for f (the monoid operation). -/
local instance group_mul_op_inst {α : Type} [EqvOp α] [Group.Ops α] : Mul α := {
  mul := f
}

class Group.Props (α : Type) [EqvOp α] [Ops α] where
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identityL {x : α} : e * x ≃ x
  identityR {x : α} : x * e ≃ x
  inverse : (x : α) → α
  inverse_propL (x : α) : (inverse x) * x ≃ e
  inverse_propR (x : α) : x * (inverse x) ≃ e

export Group.Props (
  substL substR assoc identityL identityR inverse inverse_propL inverse_propR
)

class Group (α : Type) [EqvOp α] where
  toOps : Group.Ops α
  toProps : Group.Props α

attribute [instance] Group.toOps
attribute [instance] Group.toProps

/-! ### Properties -/

variable {α : Type} [EqvOp α] [g : Group α]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
instance group_subst_inst : AA.Substitutive₂ (α := α) (f) AA.tc (· ≃ ·) (· ≃ ·)
  := {
    substitutiveL := { subst₂ := λ (_ : True) => substL }
    substitutiveR := { subst₂ := λ (_ : True) => substR }
  }

def group_mul_identity_unique {x : α}
    (x_is_left_identity : ((y : α) → (x * y) ≃ y)) : x ≃ e :=
  calc
    x    ≃   _ := Rel.symm identityR
    x * e ≃  _ := x_is_left_identity e
    e ≃      _ := Rel.refl

def group_cancellationR (x y z : α) : (x * y ≃ x * z) → y ≃ z := λ _ =>
  show y ≃ z from calc
    y     ≃                 _ := Rel.symm identityL
    e * y ≃                 _ := substL (Rel.symm (inverse_propL x))
    ((inverse x) * x) * y ≃ _ := assoc
    (inverse x) * (x * y) ≃ _ := substR ‹x * y ≃ x * z›
    (inverse x) * (x * z) ≃ _ := Rel.symm assoc
    (inverse x * x) * z   ≃ _ := substL (inverse_propL x)
    e * z ≃                 _ := identityL
    z ≃                     _ := Rel.refl

local instance monoid_from_group_ops :  CA.Monoid.Ops α := {
  f := (· * ·)
  e := g.toOps.e
}

/--
Demonstrates that any group is also a monoid.
-/
instance monoid_from_group : CA.Monoid (α := α) := {
  toOps := monoid_from_group_ops
  toProps := {
    substL    := g.toProps.substL
    substR    := g.toProps.substR
    assoc     := g.toProps.assoc
    identityL := g.toProps.identityL
    identityR := g.toProps.identityR
  }
}
