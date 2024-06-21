import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core
import Lean4Axiomatic.AbstractAlgebra.Substitutive

namespace Lean4Axiomatic.CA

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

class Monoid.Ops (α : Type) [EqvOp α] where
  f : α → α → α
  e : α
export Monoid.Ops (f e)

/-- Enables the use of the `· * ·` operator for f (the monoid operation). -/
local instance monoid_mul_op_inst {α : Type} [EqvOp α] [Monoid.Ops α] : Mul α := {
  mul := f
}

class Monoid.Props (α : Type) [EqvOp α] [Ops α] where
  substL {x y z : α} : x ≃ y → x * z ≃ y * z
  substR {x y z : α} : x ≃ y → z * x ≃ z * y
  assoc {x y z : α} : (x * y) * z ≃ x * (y * z)
  identityL {x : α} : e * x ≃ x
  identityR {x : α} : x * e ≃ x
export Monoid.Props (substL substR assoc identityL identityR)

class Monoid (α : Type) [EqvOp α] where
  toOps : Monoid.Ops α
  toProps : Monoid.Props α

attribute [instance] Monoid.toOps
attribute [instance] Monoid.toProps

/-! ### Properties -/

variable {α : Type} [EqvOp α] [m : Monoid α]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. -/
instance monoid_subst_inst : AA.Substitutive₂ (α := α) (f) AA.tc (· ≃ ·) (· ≃ ·) := {
  substitutiveL := { subst₂ := λ (_ : True) => substL }
  substitutiveR := { subst₂ := λ (_ : True) => substR }
}

/-- There is only one element, namely the identity e, such that e * x ≃ e
for all elements x. -/
def mul_identity_unique
    {x : α} (x_is_left_identity : ((y : α) → (x * y) ≃ y)) :
    x ≃ e :=
  calc
    x    ≃   _ := Rel.symm identityR
    x * e ≃  _ := x_is_left_identity e
    e ≃      _ := Rel.refl
