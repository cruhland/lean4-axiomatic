import Lean4Axiomatic.Function
import Lean4Axiomatic.Integer.Subtraction

/-!
# Integer induction

We don't usually think of integers as obeying an induction principle like the
natural numbers. But if we consider induction from the viewpoint of type
theory, another definition is what's called the _dependent eliminator_ for a
type. That's a function which, given a family of types `motive : ℤ → Sort u`,
and some important assumptions, gives back a function `(a : ℤ) → motive a`,
showing that there's an inhabitant of the family for every integer. This can be
used to prove properties which hold for all integers, or define functions that
take integers as inputs.

The reason why this is useful is the "important assumptions" piece. For
integers, that means the existence of a function
`(n m : ℕ) → motive ((n:ℤ) - (m:ℤ))` that behaves in a "reasonable" way.
Integer induction says that if you can define such a function, showing `motive`
is inhabited for all inputs of the form `(n:ℤ) - (m:ℤ)`, then you've done all
the work needed to show `motive` is inhabited for all integers. Put another
way, it says that all integers can be expressed in the form `n - m` for some
natural numbers `n` and `m`. This is quite helpful as it's often simpler to
show a result holds for natural numbers than for integers.
-/

namespace Lean4Axiomatic.Integer

open Function (IndexedFamily fsubst)
open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

/-- TODO -/
class Induction.Context
    {ℕ : outParam Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (motive : ℤ → Sort u) [IndexedFamily motive]
    :=
  /-- TODO -/
  on_diff (n m : ℕ) : motive (n - m)

  /-- TODO -/
  on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ} {diff_eqv : (n₁:ℤ) - m₁ ≃ n₂ - m₂}
    : fsubst diff_eqv (on_diff n₁ m₁) ≃ on_diff n₂ m₂

/-- TODO -/
def ind_context_prop
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Prop} [IndexedFamily motive]
    (on_diff : (n m : ℕ) → motive (n - m))
    : Induction.Context motive
    := {
  on_diff := on_diff
  on_diff_subst := Rel.refl
}

/-- TODO -/
def ind_context_const
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {X : Sort u} [EqvOp X] {on_diff : ℕ → ℕ → X}
    (on_diff_subst :
      {n₁ m₁ n₂ m₂ : ℕ} → (n₁:ℤ) - m₁ ≃ n₂ - m₂ →
      on_diff n₁ m₁ ≃ on_diff n₂ m₂)
    : Induction.Context (λ (_ : ℤ) => X)
    := {
  on_diff := on_diff
  on_diff_subst := λ {_} {_} {_} {_} {diff_eqv} => on_diff_subst diff_eqv
}

/-- Operations pertaining to eliminators on integers. -/
class Induction.Ops
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  /-- TODO -/
  ind_diff
    {motive : ℤ → Sort u} [IndexedFamily motive] (ctx : Context motive) (a : ℤ)
    : motive a

/-- TODO -/
def Induction.Context.ind_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    [Ops ℤ] {motive : ℤ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → (a : ℤ) → motive a
    :=
  Ops.ind_diff

/-- Properties of integer eliminators. -/
class Induction.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    [Ops ℤ]
    :=
  /-- TODO -/
  ind_diff_eval
    {motive : ℤ → Sort u} [IndexedFamily motive] (ctx : Context motive)
    {n m : ℕ}
    : ctx.ind_diff (n - m) ≃ ctx.on_diff n m

  /-- TODO -/
  ind_diff_subst
    {motive : ℤ → Sort u} [IndexedFamily motive] {ctx : Context motive}
    {a₁ a₂ : ℤ} {a_eqv : a₁ ≃ a₂}
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂

/-- All integer induction/eliminator axioms. -/
class Induction
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  toOps : Induction.Ops ℤ
  toProps : Induction.Props ℤ

attribute [instance] Induction.toOps
attribute [instance] Induction.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]
    [Negation ℤ] [Sign ℤ] [Subtraction ℤ] [Induction ℤ]

/-- TODO -/
def Induction.Context.ind_diff_eval
    {motive : ℤ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → {n m : ℕ} →
      ctx.ind_diff (n - m) ≃ ctx.on_diff n m
    :=
  Induction.Props.ind_diff_eval

/-- TODO -/
def Induction.Context.ind_diff_subst
    {motive : ℤ → Sort u} [IndexedFamily motive]
    (ctx : Context motive) {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂)
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂
    :=
  Induction.Props.ind_diff_subst (ctx := ctx) (a_eqv := a_eqv)

/-- TODO -/
def Induction.Context.rec_diff
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℤ) => X))
    : ℤ → X
    :=
  ctx.ind_diff

/-- TODO -/
def Induction.Context.rec_diff_eval
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℤ) => X))
    : {n m : ℕ} → ctx.rec_diff (n - m) ≃ ctx.on_diff n m
    :=
  ctx.ind_diff_eval

/-- TODO -/
def Induction.Context.rec_diff_subst
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℤ) => X))
    : {a₁ a₂ : ℤ} → (a_eqv : a₁ ≃ a₂) → ctx.rec_diff a₁ ≃ ctx.rec_diff a₂
    :=
  ctx.ind_diff_subst

end Lean4Axiomatic.Integer
