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

open Relation.Equivalence (EqvOp eqvOp_prop_term_inst)

/-! ## Axioms -/

-- TODO: Operations should maybe be pulled out from properties
-- Want to avoid the `d.C.motive_subst` ugliness
class InductionAlt.Constraints
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (motive : ℤ → Sort u) (motive_eqv : {a : ℤ} → EqvOp (motive a))
    :=
  /-- TODO -/
  motive_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → motive a₁ → motive a₂

  /-- TODO -/
  motive_subst_refl {a : ℤ} {ma : motive a} : motive_subst Rel.refl ma ≃ ma

  /-- TODO -/
  motive_subst_compose
    {a b c : ℤ} {ma : motive a} {ab : a ≃ b} {bc : b ≃ c} :
    motive_subst ‹b ≃ c› (motive_subst ‹a ≃ b› ma) ≃
    motive_subst (Rel.trans ‹a ≃ b› ‹b ≃ c›) ma

  /-- TODO -/
  motive_subst_substR
    {a b : ℤ} {ma : motive a} {mb : motive b} {ab : a ≃ b} {bc : b ≃ c} :
    motive_subst ‹a ≃ b› ma ≃ mb →
    motive_subst ‹b ≃ c› (motive_subst ‹a ≃ b› ma) ≃ motive_subst ‹b ≃ c› mb

  on_diff (n m : ℕ) : motive ((n:ℤ) - (m:ℤ))

  /-- TODO -/
  on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ} (diff_eqv : (n₁:ℤ) - (m₁:ℤ) ≃ (n₂:ℤ) - (m₂:ℤ)) :
    motive_subst diff_eqv (on_diff n₁ m₁) ≃ on_diff n₂ m₂

-- TODO: What type parameters should be made explicit?
/-- TODO -/
class InductionAlt.Data
    {ℕ : Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  motive : ℤ → Sort u

  motive_eqv {a : ℤ} : EqvOp (motive a)

  C : Constraints motive motive_eqv

-- TODO: What type parameters should be made explicit?
/-- TODO -/
class InductionAlt.ConstData
    {ℕ : Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  X : Sort u

  eqv : EqvOp X

  C : Constraints (ℤ := ℤ) (λ _ => X) eqv

  /-- TODO -/
  motive_subst_const
    {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂) (x : X) : C.motive_subst ‹a₁ ≃ a₂› x ≃ x

export InductionAlt.ConstData (motive_subst_const)

-- TODO: Looks like with a `ℤ → Prop` motive, `on_diff` can be anything,
-- because substitution for it is trivial. Evidence that the `on_diff` stuff
-- should be separated out, it would make proofs much cleaner.
def ind_constraints_prop
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Prop} {on_diff : (n m : ℕ) → motive (n - m)}
    (motive_subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → motive a₁ → motive a₂) :
    InductionAlt.Data ℤ
    := {
  motive := motive
  motive_eqv := eqvOp_prop_term_inst
  C := {
    motive_subst := motive_subst
    motive_subst_refl := rfl
    motive_subst_compose := rfl
    motive_subst_substR := λ _ => rfl
    on_diff := on_diff
    on_diff_subst := λ _ => rfl
  }
}

def ind_constraints_const
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {X : Sort u} [EqvOp X] {on_diff : ℕ → ℕ → X}
    (on_diff_subst :
      {n₁ m₁ n₂ m₂ : ℕ} → (n₁:ℤ) - m₁ ≃ n₂ - m₂ →
      on_diff n₁ m₁ ≃ on_diff n₂ m₂) :
    InductionAlt.ConstData ℤ
    := {
  X := X
  eqv := ‹EqvOp X›
  C := {
    motive_subst := λ _ => id
    motive_subst_refl := Rel.refl
    motive_subst_compose := Rel.refl
    motive_subst_substR := id
    on_diff := on_diff
    on_diff_subst := on_diff_subst
  }
  motive_subst_const := λ _ _ => Rel.refl
}

/-- Operations pertaining to eliminators on integers. -/
class InductionAlt.Ops
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] :=
  /-- TODO -/
  ind_diff (d : Data ℤ) (a : ℤ) : d.motive a

export InductionAlt.Ops (ind_diff)

/-- Properties of integer eliminators. -/
class InductionAlt.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] [ops : Ops ℤ]
    :=
  /-- TODO -/
  ind_diff_eval (d : Data ℤ) {n m : ℕ} : ind_diff d (n - m) ≃ d.C.on_diff n m

  ind_diff_subst
    (d : Data ℤ) {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂) :
    d.C.motive_subst ‹a₁ ≃ a₂› (ind_diff d a₁) ≃ ind_diff d a₂

export InductionAlt.Props (ind_diff_eval ind_diff_subst)

/-- All integer induction/eliminator axioms. -/
class InductionAlt
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  toOps : InductionAlt.Ops ℤ
  toProps : InductionAlt.Props ℤ

attribute [instance] InductionAlt.toOps
attribute [instance] InductionAlt.toProps

/-! ## Derived properties -/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Multiplication (ℕ := ℕ) ℤ]
variable [Negation ℤ] [Sign ℤ] [Subtraction ℤ] [InductionAlt ℤ]

-- TODO: Do we need the ind_on, rec_on functions?
-- Depends on if we can use `apply` cleanly in proofs
/-- TODO -/
def ind_diff_on (d : InductionAlt.Data ℤ) : d.motive a := ind_diff d a

/-- TODO -/
theorem ind_diff_on_eval
    {motive : ℤ → Sort u} {motive_eqv : {a : ℤ} → EqvOp (motive a)}
    {n m : ℕ} {on_diff : (k j : ℕ) → motive ((k:ℤ) - (j:ℤ))}
    [InductionAlt.Data @motive_eqv on_diff] :
    ind_diff_on ((n:ℤ) - (m:ℤ)) on_diff ≃ on_diff n m
    := calc
  _ = ind_diff_on ((n:ℤ) - (m:ℤ)) on_diff := rfl
  _ = ind_diff on_diff ((n:ℤ) - (m:ℤ))    := rfl
  _ ≃ on_diff n m                         := ind_diff_eval

/-- TODO -/
def rec_diff
    {X : Type u} [motive_eqv : EqvOp X]
    (on_diff : ℕ → ℕ → X)
    [InductionAlt.Data (ℤ := ℤ) (λ {_} => motive_eqv) on_diff] : ℤ → X
    :=
  ind_diff (motive := λ _ => X) on_diff

/-- TODO -/
theorem rec_diff_eval
    {X : Type u} [motive_eqv : EqvOp X] {n m : ℕ} {on_diff : ℕ → ℕ → X}
    [InductionAlt.Data (ℤ := ℤ) (λ {_} => motive_eqv) on_diff] :
    rec_diff on_diff ((n:ℤ) - (m:ℤ)) ≃ on_diff n m
    := by
  let diff := (n:ℤ) - (m:ℤ)
  calc
    _ = rec_diff on_diff diff                      := rfl
    _ = ind_diff (motive := λ _ => X) on_diff diff := rfl
    _ ≃ on_diff n m                                := ind_diff_eval

theorem rec_diff_subst
    {X : Type u} [EqvOp X] {on_diff : ℕ → ℕ → X} {a₁ a₂ : ℤ}
    [InductionAlt.ConstData (ℤ := ℤ) on_diff] : a₁ ≃ a₂ →
    rec_diff on_diff a₁ ≃ rec_diff on_diff a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show rec_diff on_diff a₁ ≃ rec_diff on_diff a₂
  calc
    _ = rec_diff on_diff a₁                      := rfl
    _ = ind_diff (motive := λ _ => X) on_diff a₁ := rfl
    _ ≃ motive_subst (motive := λ _ => X) on_diff ‹a₁ ≃ a₂› (ind_diff (motive := λ _ => X) on_diff a₁) := Rel.symm (motive_subst_const (X := X) (on_diff := on_diff) ‹a₁ ≃ a₂› (ind_diff (motive := λ _ => X) on_diff a₁))
    _ ≃ ind_diff (motive := λ _ => X) on_diff a₂ := ind_diff_subst (motive := λ _ => X) ‹a₁ ≃ a₂›
    _ = rec_diff on_diff a₂                      := rfl

/-- TODO -/
def rec_diff_on
    {X : Type u} [EqvOp X]
    (a : ℤ) (on_diff : (n m : ℕ) → X)
    [InductionAlt.Data (ℤ := ℤ) (λ {_} => ‹EqvOp X›) on_diff] : X
    :=
  rec_diff on_diff a

/-- TODO -/
theorem rec_diff_on_eval
    {X : Type u} [motive_eqv : EqvOp X] {n m : ℕ} {on_diff : ℕ → ℕ → X}
    [InductionAlt.Data (ℤ := ℤ) (λ {_} => motive_eqv) on_diff] :
    rec_diff_on ((n:ℤ) - (m:ℤ)) on_diff ≃ on_diff n m
    := calc
  _ = rec_diff_on ((n:ℤ) - (m:ℤ)) on_diff := rfl
  _ = rec_diff on_diff ((n:ℤ) - (m:ℤ))    := rfl
  _ ≃ on_diff n m                         := rec_diff_eval

theorem rec_diff_on_subst
    {X : Type u} [motive_eqv : EqvOp X] {on_diff : ℕ → ℕ → X} {a₁ a₂ : ℤ}
    [InductionAlt.ConstData (ℤ := ℤ) on_diff] : a₁ ≃ a₂ →
    rec_diff_on a₁ on_diff ≃ rec_diff_on a₂ on_diff
    := by
  intro (_ : a₁ ≃ a₂)
  show rec_diff_on a₁ on_diff ≃ rec_diff_on a₂ on_diff
  calc
    _ = rec_diff_on a₁ on_diff := rfl
    _ = rec_diff on_diff a₁    := rfl
    _ ≃ rec_diff on_diff a₂    := rec_diff_subst ‹a₁ ≃ a₂›
    _ = rec_diff_on a₂ on_diff := rfl

end Lean4Axiomatic.Integer