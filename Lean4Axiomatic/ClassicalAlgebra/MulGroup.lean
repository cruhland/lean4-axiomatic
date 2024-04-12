import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core
import Lean4Axiomatic.AbstractAlgebra.Substitutive
import Lean4Axiomatic.ClassicalAlgebra.MulMonoid

namespace Lean4Axiomatic.CA

open Relation.Equivalence (EqvOp)

/-! ### Definitions -/

class MulGroup (α : Type) [EqvOp α] extends CA.MulMonoid (α := α) where
  inverse : (x : α) → α
  inverse_propL (x : α) : (inverse x) ** x ≃ e
  inverse_propR (x : α) : x ** (inverse x) ≃ e
export MulGroup (inverse inverse_propL)

/-! ### Properties -/

def group_cancellationR [EqvOp α] (g : MulGroup α)
    (x y z : α) : (x ** y ≃ x ** z) → y ≃ z := λ _ =>
  show y ≃ z from calc
    y     ≃                   _ := Rel.symm g.identityL
    CA.MulMonoid.e ** y ≃     _ := AA.substL (Rel.symm (inverse_propL x))
    ((inverse x) ** x) ** y ≃ _ := g.assoc
    (inverse x) ** (x ** y) ≃ _ := AA.substR ‹x ** y ≃ x ** z›
    (inverse x) ** (x ** z) ≃ _ := Rel.symm g.assoc
    (inverse x ** x) ** z ≃   _ := AA.substL (inverse_propL x)
    (CA.MulMonoid.e) ** z ≃   _ := g.identityL
    z ≃                       _ := Rel.refl
