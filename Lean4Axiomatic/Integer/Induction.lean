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

export IndexedFamily (fsubst)

-- TODO: Operations should maybe be pulled out from properties
class Induction.Constraints
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (motive : ℤ → Sort u) [IndexedFamily motive] --(motive_eqv : outParam ({a : ℤ} → EqvOp (motive a)))
    :=

  on_diff (n m : ℕ) : motive ((n:ℤ) - (m:ℤ))

  /-- TODO -/
  on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ} (diff_eqv : (n₁:ℤ) - (m₁:ℤ) ≃ (n₂:ℤ) - (m₂:ℤ))
    : fsubst diff_eqv (on_diff n₁ m₁) ≃ on_diff n₂ m₂

-- TODO: What type parameters should be made explicit?
/-- TODO -/
class Induction.Data
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  motive : ℤ → Sort u
  motive_fam : IndexedFamily motive
  C : Constraints motive

attribute [instance] Induction.Data.motive_fam

-- TODO: the motive_subst definitions can be removed; use the IndexedFamily
-- members directly
def Induction.Data.motive_subst
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (d : Data ℤ) {a₁ a₂ : ℤ}
    : a₁ ≃ a₂ → motive a₁ → motive a₂
    :=
  d.C.motive_subst

def Induction.Data.motive_subst_refl
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (d : Data ℤ) {a : ℤ} {ma : motive a}
    : d.motive_subst Rel.refl ma ≃ ma
    :=
  d.C.motive_subst_refl

def Induction.Data.motive_subst_compose
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (d : Data ℤ) {a b c : ℤ} {ma : motive a} {ab : a ≃ b} {bc : b ≃ c}
    : d.motive_subst ‹b ≃ c› (d.motive_subst ‹a ≃ b› ma) ≃
      d.motive_subst (Rel.trans ‹a ≃ b› ‹b ≃ c›) ma
    :=
  d.C.motive_subst_compose

def Induction.Data.motive_subst_substR
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (d : Data ℤ) {a b c : ℤ} {ab : a ≃ b} {bc : b ≃ c}
    {ma : motive a} {mb : motive b}
    : d.motive_subst ‹a ≃ b› ma ≃ mb →
      d.motive_subst ‹b ≃ c› (d.motive_subst ‹a ≃ b› ma) ≃
        d.motive_subst ‹b ≃ c› mb
    :=
  d.C.motive_subst_substR

def Induction.Data.on_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (d : Data ℤ) : (n m : ℕ) → d.motive (n - m)
    :=
  d.C.on_diff

def Induction.Data.on_diff_subst
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (d : Data ℤ)
    {n₁ m₁ n₂ m₂ : ℕ} (diff_eqv : (n₁:ℤ) - (m₁:ℤ) ≃ (n₂:ℤ) - (m₂:ℤ))
    : d.motive_subst diff_eqv (d.on_diff n₁ m₁) ≃ d.on_diff n₂ m₂
    :=
  d.C.on_diff_subst diff_eqv

-- TODO: What type parameters should be made explicit?
/-- TODO -/
class Induction.ConstData
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : outParam Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  X : Sort u
  -- TODO: Make a trivial instance of `IndexedFamily` for constant functions
  C : Constraints (ℤ := ℤ) (λ _ => X)

def Induction.ConstData.motive_subst
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (cd : ConstData ℤ) : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → cd.X → cd.X
    :=
  cd.C.motive_subst

def Induction.ConstData.on_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (cd : ConstData ℤ) : ℕ → ℕ → cd.X
    :=
  cd.C.on_diff

/-- TODO -/
def Induction.ConstData.toData
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (cd : ConstData ℤ) : Data ℤ
    := {
  motive := λ _ => cd.X
  C := cd.C
}

-- TODO: Looks like with a `ℤ → Prop` motive, `on_diff` can be anything,
-- because substitution for it is trivial. Evidence that the `on_diff` stuff
-- should be separated out, it would make proofs much cleaner.
def ind_constraints_prop
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Prop}
    (motive_subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → motive a₁ → motive a₂)
    (on_diff : (n m : ℕ) → motive (n - m))
    : Induction.Data ℤ
    := {
  motive := motive
  -- TODO: replace with IndexedFamily
  -- motive_eqv := Relation.Equivalence.eqvOp_prop_term
  C := {
    --motive_subst := motive_subst
    --motive_subst_refl := rfl
    --motive_subst_compose := rfl
    --motive_subst_substR := λ _ => rfl
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
    Induction.ConstData ℤ
    := {
  X := X
  -- eqv := ‹EqvOp X›
  C := {
    --motive_subst := λ _ => id
    --motive_subst_refl := Rel.refl
    --motive_subst_compose := Rel.refl
    --motive_subst_substR := id
    on_diff := on_diff
    on_diff_subst := on_diff_subst
  }
}

/-- Operations pertaining to eliminators on integers. -/
class Induction.Ops
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] :=
  /-- TODO -/
  ind_diff (d : Data ℤ) (a : ℤ) : d.motive a

def Induction.Data.ind_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    [Ops ℤ] : (d : Data ℤ) → (a : ℤ) → d.motive a
    :=
  Ops.ind_diff

/-- Properties of integer eliminators. -/
class Induction.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] [ops : Ops ℤ]
    :=
  /-- TODO -/
  ind_diff_eval (d : Data ℤ) {n m : ℕ} : d.ind_diff (n - m) ≃ d.on_diff n m

  ind_diff_subst
    (d : Data ℤ) {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂) :
    d.motive_subst ‹a₁ ≃ a₂› (d.ind_diff a₁) ≃ d.ind_diff a₂

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

def Induction.Data.ind_diff_eval :
    (d : Data ℤ) → {n m : ℕ} → d.ind_diff (n - m) ≃ d.on_diff n m
    :=
  Induction.Props.ind_diff_eval

def Induction.Data.ind_diff_subst :
    (d : Data ℤ) → {a₁ a₂ : ℤ} → (a_eqv : a₁ ≃ a₂) →
    d.motive_subst ‹a₁ ≃ a₂› (d.ind_diff a₁) ≃ d.ind_diff a₂
    :=
  Induction.Props.ind_diff_subst

def Induction.ConstData.rec_diff (cd : ConstData ℤ) : ℤ → cd.X :=
  cd.toData.ind_diff

def Induction.ConstData.rec_diff_eval
    (cd : ConstData ℤ) : {n m : ℕ} → cd.rec_diff (n - m) ≃ cd.on_diff n m
    :=
  cd.toData.ind_diff_eval

def Induction.ConstData.rec_diff_subst
    (cd : ConstData ℤ) : {a₁ a₂ : ℤ} → (a_eqv : a₁ ≃ a₂) →
    cd.motive_subst ‹a₁ ≃ a₂› (cd.rec_diff a₁) ≃ cd.rec_diff a₂
    :=
  cd.toData.ind_diff_subst

end Lean4Axiomatic.Integer
