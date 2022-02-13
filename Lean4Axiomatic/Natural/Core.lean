import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv

namespace Lean4Axiomatic
namespace Natural

open Relation (EqvOp?)

variable {ℕ : Type}

class Constructors (ℕ : Type) where
  zero : ℕ
  step : ℕ → ℕ

export Constructors (zero step)

def ofNat {ℕ : Type} [Constructors ℕ] : Nat → ℕ
| 0 => zero
| n+1 => step (ofNat n)

instance instOfNat {ℕ : Type} [Constructors ℕ] {n : Nat} : OfNat ℕ n where
  ofNat := ofNat n

class Equality (ℕ : Type) where
  eqvOp? : EqvOp? ℕ

attribute [instance] Equality.eqvOp?

class Core (ℕ : Type) extends Constructors ℕ, Equality ℕ

class Axioms.Base (ℕ : Type) [Core ℕ] where
  step_substitutive : AA.Substitutive (α := ℕ) step (· ≃ ·) (· ≃ ·)
  step_injective : AA.Injective (α := ℕ) step (· ≃ ·) (· ≃ ·)
  step_neq_zero {n : ℕ} : step n ≄ 0

  ind {motive : ℕ → Prop}
    : motive 0 → (∀ n, motive n → motive (step n)) → ∀ n, motive n

attribute [instance] Axioms.Base.step_substitutive
attribute [instance] Axioms.Base.step_injective

class Axioms.Derived (ℕ : Type) [Core ℕ] extends Axioms.Base ℕ where
  ind_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n

  cases_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n

  step_neq {n : ℕ} : step n ≄ n

namespace Axioms
export Axioms.Base (ind step_injective step_neq_zero)
export Axioms.Derived (cases_on ind_on)
end Axioms

export Axioms (ind step_injective step_neq_zero)

end Natural
end Lean4Axiomatic
