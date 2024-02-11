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

open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

class IndexedFamily {α : Type} [EqvOp α] (fam : α → Sort u) :=
  fam_eqv {x : α} : EqvOp (fam x)

  fsubst {x₁ x₂ : α} : x₁ ≃ x₂ → fam x₁ → fam x₂

  fsubst_refl {x : α} {fx : fam x} : fsubst Rel.refl fx ≃ fx

  fsubst_trans
    {x y z : α} {xy : x ≃ y} {yz : y ≃ z} {fx : fam x}
    : fsubst ‹y ≃ z› (fsubst ‹x ≃ y› fx) ≃
      fsubst (Rel.trans ‹x ≃ y› ‹y ≃ z›) fx

  fsubst_substR
    {x y : α} {xy : x ≃ y} {fx₁ fx₂ : fam x}
    : fx₁ ≃ fx₂ → fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂

  fsubst_injectR
    {x y : α} {xy : x ≃ y} {fx₁ fx₂ : fam x}
    : fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ → fx₁ ≃ fx₂

attribute [instance] IndexedFamily.fam_eqv

export IndexedFamily (
  fsubst fsubst_injectR fsubst_refl fsubst_substR fsubst_trans
)

instance idx_fam_const_inst
    {α : Type} [EqvOp α] {X : Sort u} [EqvOp X]
    : IndexedFamily (λ (_ : α) => X)
    := {
  fam_eqv := λ {_} => ‹EqvOp X›
  fsubst := λ _ => id
  fsubst_refl := Rel.refl
  fsubst_trans := Rel.refl
  fsubst_substR := id
  fsubst_injectR := id
}

def idx_fam_prop
    {α : Type} [EqvOp α] {fam : α → Prop}
    (fsubst : {x₁ x₂ : α} → x₁ ≃ x₂ → fam x₁ → fam x₂)
    : IndexedFamily fam
    := {
  fam_eqv := Relation.Equivalence.eqvOp_prop_term
  fsubst := fsubst
  fsubst_refl := rfl
  fsubst_trans := rfl
  fsubst_substR := λ _ => rfl
  fsubst_injectR := λ _ => rfl
}

-- TODO: Operations should maybe be pulled out from properties
class Induction.Constraints
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (motive : ℤ → Sort u) [IndexedFamily motive]
    :=

  on_diff (n m : ℕ) : motive ((n:ℤ) - (m:ℤ))

  /-- TODO -/
  on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ} {diff_eqv : (n₁:ℤ) - (m₁:ℤ) ≃ (n₂:ℤ) - (m₂:ℤ)}
    : fsubst diff_eqv (on_diff n₁ m₁) ≃ on_diff n₂ m₂

-- TODO: What type parameters should be made explicit?
/-- TODO -/
class Induction.Data
    {ℕ : outParam Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (motive : ℤ → Sort u) [fam : IndexedFamily motive]
    :=
  C : Constraints motive

def Induction.Data.on_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Sort u} [IndexedFamily motive] (d : Data motive)
    : (n m : ℕ) → motive (n - m)
    :=
  d.C.on_diff

def Induction.Data.on_diff_subst
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Sort u} [IndexedFamily motive] (d : Data motive)
    {n₁ m₁ n₂ m₂ : ℕ} {diff_eqv : (n₁:ℤ) - (m₁:ℤ) ≃ (n₂:ℤ) - (m₂:ℤ)}
    : fsubst diff_eqv (d.on_diff n₁ m₁) ≃ d.on_diff n₂ m₂
    :=
  d.C.on_diff_subst

def Induction.ConstData
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (X : Sort u) [EqvOp X]
    : Sort (max 1 u)
    :=
  Data (λ (_ : ℤ) => X)

-- TODO: Looks like with a `ℤ → Prop` motive, `on_diff` can be anything,
-- because substitution for it is trivial. Evidence that the `on_diff` stuff
-- should be separated out, it would make proofs much cleaner.
def ind_constraints_prop
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Prop} [IndexedFamily motive]
    (on_diff : (n m : ℕ) → motive (n - m))
    : Induction.Data motive
    :=
  {
    C := {
      on_diff := on_diff
      on_diff_subst := Rel.refl
    }
  }

def ind_constraints_const
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {X : Sort u} [EqvOp X] {on_diff : ℕ → ℕ → X}
    (on_diff_subst :
      {n₁ m₁ n₂ m₂ : ℕ} → (n₁:ℤ) - m₁ ≃ n₂ - m₂ →
      on_diff n₁ m₁ ≃ on_diff n₂ m₂) :
    Induction.Data (λ (_ : ℤ) => X)
    := {
  C := {
    on_diff := on_diff
    on_diff_subst := λ {_} {_} {_} {_} {diff_eqv} => on_diff_subst diff_eqv
  }
}

/-- Operations pertaining to eliminators on integers. -/
class Induction.Ops
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  /-- TODO -/
  ind_diff
    {motive : ℤ → Sort u} [IndexedFamily motive] (d : Data motive) (a : ℤ)
    : motive a

-- TODO: Export `ind_diff` would give the same effect as this?
def Induction.Data.ind_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    [Ops ℤ] {motive : ℤ → Sort u} [IndexedFamily motive]
    : (d : Data motive) → (a : ℤ) → motive a
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
    {motive : ℤ → Sort u} [IndexedFamily motive] (d : Data motive) {n m : ℕ}
    : d.ind_diff (n - m) ≃ d.on_diff n m

  /-- TODO -/
  ind_diff_subst
    {motive : ℤ → Sort u} [IndexedFamily motive] (d : Data motive)
    {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂)
    : fsubst ‹a₁ ≃ a₂› (d.ind_diff a₁) ≃ d.ind_diff a₂

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

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Multiplication (ℕ := ℕ) ℤ]
variable [Negation ℤ] [Sign ℤ] [Subtraction ℤ] [Induction ℤ]

-- TODO: export `ind_diff_eval` gives the same effect?
def Induction.Data.ind_diff_eval
    {motive : ℤ → Sort u} [IndexedFamily motive]
    : (d : Data motive) → {n m : ℕ} → d.ind_diff (n - m) ≃ d.on_diff n m
    :=
  Induction.Props.ind_diff_eval

-- TODO: export `ind_diff_subst` gives the same effect?
def Induction.Data.ind_diff_subst
    {motive : ℤ → Sort u} [IndexedFamily motive]
    : (d : Data motive) → {a₁ a₂ : ℤ} → (a_eqv : a₁ ≃ a₂) →
      fsubst ‹a₁ ≃ a₂› (d.ind_diff a₁) ≃ d.ind_diff a₂
    :=
  Induction.Props.ind_diff_subst

def Induction.ConstData.rec_diff
    {X : Sort u} [EqvOp X] (cd : ConstData ℤ X)
    : ℤ → X
    :=
  cd.ind_diff

def Induction.ConstData.rec_diff_eval
    {X : Sort u} [EqvOp X] (cd : ConstData ℤ X)
    : {n m : ℕ} → cd.rec_diff (n - m) ≃ cd.on_diff n m
    :=
  cd.ind_diff_eval

def Induction.ConstData.rec_diff_subst
    {X : Sort u} [EqvOp X] (cd : ConstData ℤ X)
    : {a₁ a₂ : ℤ} → (a_eqv : a₁ ≃ a₂) → cd.rec_diff a₁ ≃ cd.rec_diff a₂
    :=
  cd.ind_diff_subst

end Lean4Axiomatic.Integer
