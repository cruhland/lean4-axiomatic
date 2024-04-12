import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core
import Lean4Axiomatic.AbstractAlgebra.Substitutive

namespace Lean4Axiomatic.CA

open Relation.Equivalence (EqvOp)

/-!
An attempt at formalizing traditional algebraic structures
such as groups and rings.

Here we introduce a Monoid using a muliplication-like notation.

Note that we only need a binary operation that is associative and
has identities.  So for instance, natural numbers with the addition
operator conforms to the requirements of MulMonoid.
-/

/-! ### Definitions -/

class MulMonoid (α : Type) [EqvOp α] where
  f : α → α → α
  e : α
  fs : AA.Substitutive₂ (α := α) f AA.tc (· ≃ ·) (· ≃ ·)
  assoc {x y z : α} : f (f x y) z ≃ f x (f y z)
  identityL {x : α} : f e x ≃ x
  identityR {x : α} : f x e ≃ x

attribute [instance] MulMonoid.fs

export MulMonoid (f e fs assoc identityL identityR)

/--
An infixl notation is introduced for the main algrebraic operation f,
and using a mulitplication-like symbol is standard, especially for
ones where commutativity is not assured, and is much more convient than
function application.

Note: Using '**' so as not to interfere with * which is already in scope
from built-in libraries (see HMul)
-/
infixl:70 " ** " => f

/-! ### Properties -/

def mul_identity_unique {α : Type} [EqvOp α] {m : MulMonoid α}
    {x : α} (x_is_identity : ((y : α) → (x ** y) ≃ y)) :
    x ≃ e :=
  calc
    x    ≃    _ := Rel.symm m.identityR
    x ** e ≃  _ := ‹(y : α) → (x ** y) ≃ y› e
    e ≃       _ := Rel.refl
