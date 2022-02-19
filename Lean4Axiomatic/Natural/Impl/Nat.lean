import Lean4Axiomatic.Eqv
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Default
import Lean4Axiomatic.Natural.Impl.Derived

open Relation (EqvOp?)

namespace Lean4Axiomatic
namespace Natural
namespace Impl
namespace Nat

instance constructors : Constructors Nat where
  zero := Nat.zero
  step := Nat.succ

instance eqvOp? : EqvOp? Nat where
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq

instance equality : Equality Nat where
  eqvOp? := eqvOp?

instance : Core Nat := Core.mk

instance step_substitutive
    : AA.Substitutive (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  subst := congrArg step

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

instance step_injective : AA.Injective (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  inject := succ_injective

def ind
    {motive : Nat → Sort v}
    (mz : motive 0) (ms : {n : Nat} → motive n → motive (Nat.succ n)) (n : Nat)
    : motive n :=
  match n with
  | Nat.zero => mz
  | Nat.succ n => ms (ind mz ms n)

instance axioms_base : Axioms.Base Nat where
  step_substitutive := step_substitutive
  step_injective := step_injective
  step_neq_zero := Nat.noConfusion
  -- 2022-01-11: Using `Nat.rec` directly here, gives the following error:
  -- code generator does not support recursor 'Nat.rec' yet, consider using
  -- 'match ... with' and/or structural recursion
  ind := ind

instance addition_base : Addition.Base Nat where
  addOp := _root_.instAddNat
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add

instance : Decl Nat := Decl.mk

end Nat
end Impl
end Natural
end Lean4Axiomatic
