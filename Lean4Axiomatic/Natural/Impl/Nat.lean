import Lean4Axiomatic.Eqv
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Default
import Lean4Axiomatic.Natural.Impl.Derived

open Relation (EqvOp?)

namespace Lean4Axiomatic
namespace Natural
namespace Impl
namespace Nat

instance : Constructors Nat where
  zero := Nat.zero
  step := Nat.succ

instance : EqvOp? Nat where
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq

instance : Equality Nat where
  eqvOp? := inferInstance

instance : Core Nat := Core.mk

instance : AA.Substitutive (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  subst := congrArg step

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

instance : AA.Injective (step : Nat → Nat) (· ≃ ·) (· ≃ ·) where
  inject := succ_injective

def indImpl
    {motive : Nat → Sort v}
    (mz : motive 0) (ms : {n : Nat} → motive n → motive (Nat.succ n)) (n : Nat)
    : motive n :=
  match n with
  | Nat.zero => mz
  | Nat.succ n => ms (indImpl mz ms n)

instance : Axioms.Base Nat where
  step_substitutive := inferInstance
  step_injective := inferInstance
  step_neq_zero := Nat.noConfusion
  -- 2022-01-11: Using `Nat.rec` directly here, gives the following error:
  -- code generator does not support recursor 'Nat.rec' yet, consider using
  -- 'match ... with' and/or structural recursion
  ind := indImpl

instance : Addition.Base Nat where
  addOp := inferInstance
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add

instance : Decl Nat := Decl.mk

end Nat
end Impl
end Natural
end Lean4Axiomatic
