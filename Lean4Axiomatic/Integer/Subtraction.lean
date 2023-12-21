import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Sign

/-!
# Integer subtraction
-/

namespace Lean4Axiomatic.Integer

open Relation.Equivalence (EqvOp eqvOp_prop_term_inst)

/-!
## Axioms
-/

/-- Operations pertaining to integer subtraction. -/
class Subtraction.Ops (ℤ : Type) :=
  /-- Subtraction of integers. -/
  sub : ℤ → ℤ → ℤ

export Subtraction.Ops (sub)

/-- Enables the use of the `· - ·` operator for subtraction. -/
instance sub_op_inst {ℤ : Type} [Subtraction.Ops ℤ] : Sub ℤ := {
  sub := sub
}

/-- Properties of integer subtraction. -/
class Subtraction.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Ops ℤ]
    :=
  /-- Subtraction is equivalent to addition of a negated second argument. -/
  sub_defn {a b : ℤ} : a - b ≃ a + (-b)

export Subtraction.Props (sub_defn)

/-- All integer subtraction axioms. -/
class Subtraction
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ]
    :=
  toOps : Subtraction.Ops ℤ
  toProps : Subtraction.Props ℤ

attribute [instance] Subtraction.toOps
attribute [instance] Subtraction.toProps

-- Write an alternative class for `Constraints` that serves the same purpose,
-- but gives access to the underlying natural numbers.

/-- TODO -/
class Induction.Constraints
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Sort u} (motive_eqv : outParam ({a : ℤ} → EqvOp (motive a)))
    (on_diff : (n m : ℕ) → motive ((n:ℤ) - (m:ℤ)))
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

  /-- TODO -/
  on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ} (diff_eqv : (n₁:ℤ) - (m₁:ℤ) ≃ (n₂:ℤ) - (m₂:ℤ)) :
    motive_subst diff_eqv (on_diff n₁ m₁) ≃ on_diff n₂ m₂

export Induction.Constraints (
  on_diff_subst motive_subst motive_subst_compose motive_subst_refl
  motive_subst_substR
)

/-- TODO -/
class Induction.ConstConstraints
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {X : Sort u} [EqvOp X] (on_diff : ℕ → ℕ → X)
    extends Induction.Constraints (ℤ := ℤ) (λ {_} => ‹EqvOp X›) on_diff
    :=
  /-- TODO -/
  motive_subst_const
    {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂) (x : X) : motive_subst ‹a₁ ≃ a₂› x ≃ x

export Induction.ConstConstraints (motive_subst_const)

def ind_constraints_prop
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {motive : ℤ → Prop} {on_diff : (n m : ℕ) → motive (n - m)}
    (motive_subst : {a₁ a₂ : ℤ} → a₁ ≃ a₂ → motive a₁ → motive a₂) :
    Induction.Constraints
      (motive := motive) (λ {_} => eqvOp_prop_term_inst) on_diff
    := {
  motive_subst := motive_subst
  motive_subst_refl := rfl
  motive_subst_compose := rfl
  motive_subst_substR := λ _ => rfl
  on_diff_subst := λ _ => rfl
}

def ind_constraints_const
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    {X : Sort u} [EqvOp X] {on_diff : ℕ → ℕ → X}
    (on_diff_subst :
      {n₁ m₁ n₂ m₂ : ℕ} → (n₁:ℤ) - m₁ ≃ n₂ - m₂ →
      on_diff n₁ m₁ ≃ on_diff n₂ m₂) :
    Induction.ConstConstraints (ℤ := ℤ) on_diff
    := {
  motive_subst := λ _ => id
  motive_subst_const := λ _ _ => Rel.refl
  motive_subst_refl := Rel.refl
  motive_subst_compose := Rel.refl
  motive_subst_substR := id
  on_diff_subst := on_diff_subst
}

/-- Operations pertaining to eliminators on integers. -/
class Induction.Ops
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] :=
  /-- TODO -/
  ind_diff
    {motive : ℤ → Sort u} {motive_eqv : {a : ℤ} → EqvOp (motive a)}
    (on_diff : (n m : ℕ) → motive ((n:ℤ) - (m:ℤ)))
    [Constraints @motive_eqv on_diff] (a : ℤ) : motive a

export Induction.Ops (ind_diff)

/-- Properties of integer eliminators. -/
class Induction.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] [ops : Ops ℤ]
    :=
  /-- TODO -/
  ind_diff_eval
    {motive : ℤ → Sort u} {motive_eqv : {a : ℤ} → EqvOp (motive a)}
    {on_diff : (k j : ℕ) → motive (k - j)}
    [Constraints @motive_eqv on_diff] {n m : ℕ} :
    ind_diff on_diff (n - m) ≃ on_diff n m

  ind_diff_subst
    {motive : ℤ → Sort u} {motive_eqv : {a : ℤ} → EqvOp (motive a)}
    {on_diff : (n m : ℕ) → motive (n - m)} [Constraints @motive_eqv on_diff]
    {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂) :
    motive_subst on_diff ‹a₁ ≃ a₂› (ind_diff on_diff a₁) ≃ ind_diff on_diff a₂

export Induction.Props (ind_diff_eval ind_diff_subst)

/-- All integer induction/eliminator axioms. -/
class Induction
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  toOps : Induction.Ops ℤ
  toProps : Induction.Props ℤ

attribute [instance] Induction.toOps
attribute [instance] Induction.toProps

/-!
## Derived properties
-/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Multiplication (ℕ := ℕ) ℤ]
variable [Negation ℤ] [Sign ℤ] [Subtraction ℤ] [Induction ℤ]

/-- TODO -/
def ind_diff_on
    {motive : ℤ → Sort u} {motive_eqv : {a : ℤ} → EqvOp (motive a)} (a : ℤ)
    (on_diff : (n m : ℕ) → motive ((n:ℤ) - (m:ℤ)))
    [Induction.Constraints @motive_eqv on_diff] : motive a
    :=
  ind_diff on_diff a

/-- TODO -/
theorem ind_diff_on_eval
    {motive : ℤ → Sort u} {motive_eqv : {a : ℤ} → EqvOp (motive a)}
    {n m : ℕ} {on_diff : (k j : ℕ) → motive ((k:ℤ) - (j:ℤ))}
    [Induction.Constraints @motive_eqv on_diff] :
    ind_diff_on ((n:ℤ) - (m:ℤ)) on_diff ≃ on_diff n m
    := calc
  _ = ind_diff_on ((n:ℤ) - (m:ℤ)) on_diff := rfl
  _ = ind_diff on_diff ((n:ℤ) - (m:ℤ))    := rfl
  _ ≃ on_diff n m                         := ind_diff_eval

/-- TODO -/
def rec_diff
    {X : Type u} [motive_eqv : EqvOp X]
    (on_diff : ℕ → ℕ → X)
    [Induction.Constraints (ℤ := ℤ) (λ {_} => motive_eqv) on_diff] : ℤ → X
    :=
  ind_diff (motive := λ _ => X) on_diff

/-- TODO -/
theorem rec_diff_eval
    {X : Type u} [motive_eqv : EqvOp X] {n m : ℕ} {on_diff : ℕ → ℕ → X}
    [Induction.Constraints (ℤ := ℤ) (λ {_} => motive_eqv) on_diff] :
    rec_diff on_diff ((n:ℤ) - (m:ℤ)) ≃ on_diff n m
    := by
  let diff := (n:ℤ) - (m:ℤ)
  calc
    _ = rec_diff on_diff diff                      := rfl
    _ = ind_diff (motive := λ _ => X) on_diff diff := rfl
    _ ≃ on_diff n m                                := ind_diff_eval

theorem rec_diff_subst
    {X : Type u} [EqvOp X] {on_diff : ℕ → ℕ → X} {a₁ a₂ : ℤ}
    [Induction.ConstConstraints (ℤ := ℤ) on_diff] : a₁ ≃ a₂ →
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
    [Induction.Constraints (ℤ := ℤ) (λ {_} => ‹EqvOp X›) on_diff] : X
    :=
  rec_diff on_diff a

/-- TODO -/
theorem rec_diff_on_eval
    {X : Type u} [motive_eqv : EqvOp X] {n m : ℕ} {on_diff : ℕ → ℕ → X}
    [Induction.Constraints (ℤ := ℤ) (λ {_} => motive_eqv) on_diff] :
    rec_diff_on ((n:ℤ) - (m:ℤ)) on_diff ≃ on_diff n m
    := calc
  _ = rec_diff_on ((n:ℤ) - (m:ℤ)) on_diff := rfl
  _ = rec_diff on_diff ((n:ℤ) - (m:ℤ))    := rfl
  _ ≃ on_diff n m                         := rec_diff_eval

theorem rec_diff_on_subst
    {X : Type u} [motive_eqv : EqvOp X] {on_diff : ℕ → ℕ → X} {a₁ a₂ : ℤ}
    [Induction.ConstConstraints (ℤ := ℤ) on_diff] : a₁ ≃ a₂ →
    rec_diff_on a₁ on_diff ≃ rec_diff_on a₂ on_diff
    := by
  intro (_ : a₁ ≃ a₂)
  show rec_diff_on a₁ on_diff ≃ rec_diff_on a₂ on_diff
  calc
    _ = rec_diff_on a₁ on_diff := rfl
    _ = rec_diff on_diff a₁    := rfl
    _ ≃ rec_diff on_diff a₂    := rec_diff_subst ‹a₁ ≃ a₂›
    _ = rec_diff_on a₂ on_diff := rfl

/--
Subtraction is left-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition.
-/
theorem sub_substL {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ - b ≃ a₂ - b := by
  intro (_ : a₁ ≃ a₂)
  show a₁ - b ≃ a₂ - b
  calc
    a₁ - b    ≃ _ := sub_defn
    a₁ + (-b) ≃ _ := AA.substL ‹a₁ ≃ a₂›
    a₂ + (-b) ≃ _ := Rel.symm sub_defn
    a₂ - b    ≃ _ := Rel.refl

def sub_substitutiveL
    : AA.SubstitutiveOn Hand.L (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => sub_substL
}

/--
Subtraction is right-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition and
negation.
-/
theorem sub_substR {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b - a₁ ≃ b - a₂ := by
  intro (_ : a₁ ≃ a₂)
  show b - a₁ ≃ b - a₂
  calc
    b - a₁    ≃ _ := sub_defn
    b + (-a₁) ≃ _ := AA.substR (AA.subst₁ ‹a₁ ≃ a₂›)
    b + (-a₂) ≃ _ := Rel.symm sub_defn
    b - a₂    ≃ _ := Rel.refl

def sub_substitutiveR
    : AA.SubstitutiveOn Hand.R (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => sub_substR
}

instance sub_substitutive
    : AA.Substitutive₂ (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := sub_substitutiveL
  substitutiveR := sub_substitutiveR
}

/--
Subtracting an integer from itself yields zero.

**Property and proof intuition**: This is equivalent to the additive inverse
property.
-/
theorem sub_same {a : ℤ} : a - a ≃ 0 := calc
  a - a  ≃ _ := sub_defn
  a + -a ≃ _ := AA.inverseR
  0      ≃ _ := Rel.refl

/-- TODO -/
theorem sub_identL {a : ℤ} : 0 - a ≃ -a := calc
  _ ≃ 0 - a  := Rel.refl
  _ ≃ 0 + -a := sub_defn
  _ ≃ -a     := AA.identL

/-- TODO -/
theorem sub_identR {a : ℤ} : a - 0 ≃ a := calc
  _ ≃ a - 0        := Rel.refl
  _ ≃ a + -0       := sub_defn
  _ ≃ a + (-0 + 0) := AA.substR (Rel.symm AA.identR)
  _ ≃ a + 0        := AA.substR AA.inverseL
  _ ≃ a            := AA.identR

/--
Equivalent integers are the only ones to differ by zero.

**Proof intuition**: The reverse direction is trivial; the forward direction
uses the additive inverse property and the assumption `a - b ≃ 0` to replace
`a` with `b`.
-/
theorem zero_diff_iff_eqv {a b : ℤ} : a - b ≃ 0 ↔ a ≃ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a - b ≃ 0)
    show a ≃ b
    calc
      a            ≃ _ := Rel.symm AA.identR
      a + 0        ≃ _ := AA.substR (Rel.symm AA.inverseL)
      a + (-b + b) ≃ _ := Rel.symm AA.assoc
      (a + -b) + b ≃ _ := AA.substL (Rel.symm sub_defn)
      (a - b) + b  ≃ _ := AA.substL ‹a - b ≃ 0›
      0 + b        ≃ _ := AA.identL
      b            ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ b)
    show a - b ≃ 0
    calc
      a - b  ≃ _ := AA.substL ‹a ≃ b›
      b - b  ≃ _ := sub_same
      0      ≃ _ := Rel.refl

/--
The right-hand operand of subtraction can be moved to the left-hand operand of
addition on the other side of an equivalence.

**Property intuition**: This is a very common technique in algebra.

**Proof intuition**: There's no key idea for this proof, other than using
algebra on integers to obtain expressions where assumptions can be used.
-/
theorem subR_move_addL {a b c : ℤ} : a - b ≃ c ↔ a ≃ b + c := by
  apply Iff.intro
  case mp =>
    intro (_ : a - b ≃ c)
    show a ≃ b + c
    calc
      a            ≃ _ := Rel.symm AA.identR
      a + 0        ≃ _ := AA.substR (Rel.symm AA.inverseL)
      a + (-b + b) ≃ _ := Rel.symm AA.assoc
      (a + -b) + b ≃ _ := AA.substL (Rel.symm sub_defn)
      (a - b) + b  ≃ _ := AA.substL ‹a - b ≃ c›
      c + b        ≃ _ := AA.comm
      b + c        ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ b + c)
    show a - b ≃ c
    calc
      a - b        ≃ _ := AA.substL ‹a ≃ b + c›
      b + c - b    ≃ _ := AA.substL AA.comm
      c + b - b    ≃ _ := sub_defn
      c + b + -b   ≃ _ := AA.assoc
      c + (b + -b) ≃ _ := AA.substR AA.inverseR
      c + 0        ≃ _ := AA.identR
      c            ≃ _ := Rel.refl

/-- TODO -/
theorem sub_swap_add {a b c d : ℤ} : a - b ≃ c - d ↔ a + d ≃ c + b := by
  apply Iff.intro
  case mp =>
    intro (_ : a - b ≃ c - d)
    show a + d ≃ c + b
    calc
      _ ≃ a + d              := Rel.refl
      _ ≃ (a + 0) + d        := AA.substL (Rel.symm AA.identR)
      _ ≃ (a + (-b + b)) + d := AA.substL (AA.substR (Rel.symm AA.inverseL))
      _ ≃ ((a + -b) + b) + d := AA.substL (Rel.symm AA.assoc)
      _ ≃ ((a - b) + b) + d  := AA.substL (AA.substL (Rel.symm sub_defn))
      _ ≃ ((c - d) + b) + d  := AA.substL (AA.substL ‹a - b ≃ c - d›)
      _ ≃ (c - d) + (b + d)  := AA.assoc
      _ ≃ (c + -d) + (b + d) := AA.substL sub_defn
      _ ≃ (c + b) + (-d + d) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ (c + b) + 0        := AA.substR AA.inverseL
      _ ≃ c + b              := AA.identR
  case mpr =>
    intro (_ : a + d ≃ c + b)
    show a - b ≃ c - d
    calc
      _ ≃ a - b               := Rel.refl
      _ ≃ a + -b              := sub_defn
      _ ≃ (a + 0) + -b        := AA.substL (Rel.symm AA.identR)
      _ ≃ (a + (d + -d)) + -b := AA.substL (AA.substR (Rel.symm AA.inverseR))
      _ ≃ ((a + d) + -d) + -b := AA.substL (Rel.symm AA.assoc)
      _ ≃ ((c + b) + -d) + -b := AA.substL (AA.substL ‹a + d ≃ c + b›)
      _ ≃ (c + b) + (-d + -b) := AA.assoc
      _ ≃ (c + -d) + (b + -b) := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ (c + -d) + 0        := AA.substR AA.inverseR
      _ ≃ c + -d              := AA.identR
      _ ≃ c - d               := Rel.symm sub_defn

/--
Multiplication distributes over subtraction (on the left).

**Property and proof intuition**: This is the same as multiplication
distributing over addition: just expand the definition of subtraction.
-/
theorem mul_distribL_sub {a b c : ℤ} : a * (b - c) ≃ a * b - a * c := calc
  a * (b - c)      ≃ _ := AA.substR sub_defn
  a * (b + -c)     ≃ _ := AA.distribL
  a * b + a * -c   ≃ _ := AA.substR (Rel.symm AA.scompatR)
  a * b + -(a * c) ≃ _ := Rel.symm sub_defn
  a * b - a * c    ≃ _ := Rel.refl

def mul_distributiveL_sub
    : AA.DistributiveOn Hand.L (α := ℤ) (· * ·) (· - ·)
    := {
  distrib := mul_distribL_sub
}

instance mul_distributive_sub : AA.Distributive (α := ℤ) (· * ·) (· - ·) := {
  distributiveL := mul_distributiveL_sub
  distributiveR := AA.distributiveR_from_distributiveL mul_distributiveL_sub
}

/--
When subtracting two sums, if they both have the same right-hand operand, it
can be removed, leaving just the difference of the left-hand operands.

**Intuition**: This follows from the basic algebraic properties of integers.
-/
theorem sub_sums_sameR {a b c : ℤ} : a + c - (b + c) ≃ a - b := calc
  a + c - (b + c)           ≃ _ := sub_defn
  a + c + -(b + c)          ≃ _ := AA.substR (Rel.symm mul_neg_one)
  a + c + -1 * (b + c)      ≃ _ := AA.substR AA.distribL
  a + c + (-1 * b + -1 * c) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
  a + -1 * b + (c + -1 * c) ≃ _ := AA.substR (AA.substR mul_neg_one)
  a + -1 * b + (c + -c)     ≃ _ := AA.substR AA.inverseR
  a + -1 * b + 0            ≃ _ := AA.identR
  a + -1 * b                ≃ _ := AA.substR mul_neg_one
  a + -b                    ≃ _ := Rel.symm sub_defn
  a - b                     ≃ _ := Rel.refl

/--
Multiplication by a nonzero value on the left is injective.

**Property and proof intuition**: Viewing multiplication as a scaling
operation, this says that if two values are equivalent after being scaled by
the same amount, then their unscaled values must have been equivalent as well.
This seems to be consistent with our intuitive understanding of multiplication.
-/
theorem mul_cancelL {a b c : ℤ} : a ≄ 0 → a * b ≃ a * c → b ≃ c := by
  intro (_ : a ≄ 0) (_ : a * b ≃ a * c)
  show b ≃ c
  have : a * b - a * c ≃ 0 := zero_diff_iff_eqv.mpr ‹a * b ≃ a * c›
  have : a * (b - c) ≃ 0 := Rel.trans AA.distribL ‹a * b - a * c ≃ 0›
  have : a ≃ 0 ∨ b - c ≃ 0 := mul_split_zero.mp ‹a * (b - c) ≃ 0›
  match ‹a ≃ 0 ∨ b - c ≃ 0› with
  | Or.inl (_ : a ≃ 0) =>
    show b ≃ c
    exact absurd ‹a ≃ 0› ‹a ≄ 0›
  | Or.inr (_ : b - c ≃ 0) =>
    show b ≃ c
    exact zero_diff_iff_eqv.mp ‹b - c ≃ 0›

def mul_cancellativeL
    : AA.CancellativeOn Hand.L (α := ℤ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancel := mul_cancelL
}

instance mul_cancellative
    : AA.Cancellative (α := ℤ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancellativeL := mul_cancellativeL
  cancellativeR := AA.cancelR_from_cancelL mul_cancellativeL
}

/--
Multiplication by a nonzero value on the right is injective.

**Property and proof intuition**: See `mul_cancelL`.
-/
theorem mul_cancelR {a b c : ℤ} : a ≄ 0 → b * a ≃ c * a → b ≃ c :=
  AA.cancelRC (C := (· ≄ 0))

/--
Decidable equivalence for integers.

**Property intuition**: Every integer has a finite value, so it should be
possible for an algorithm to decide if two of them are equivalent.

**Proof intuition**: The result of `sgn` is already decidable, so compute it
for `a - b` and rewrite the result into `a ≃ b` or `a ≄ b` depending on whether
the sign is zero or not.
-/
instance eqv? (a b : ℤ) : Decidable (a ≃ b) := by
  let Sgn3 := AA.OneOfThree₁ (sgn (a-b) ≃ 0) (sgn (a-b) ≃ 1) (sgn (a-b) ≃ -1)
  have : Sgn3 := sgn_trichotomy (a-b)
  match this with
  | AA.OneOfThree₁.first (_ : sgn (a-b) ≃ 0) =>
    have : a-b ≃ 0 := sgn_zero.mpr ‹sgn (a-b) ≃ 0›
    have : a ≃ b := zero_diff_iff_eqv.mp this
    have : Decidable (a ≃ b) := isTrue this
    exact this
  | AA.OneOfThree₁.second (_ : sgn (a-b) ≃ 1) =>
    have : (1:ℤ) ≄ 0 := one_neqv_zero
    have : sgn (a-b) ≄ 0 := AA.neqv_substL (Rel.symm ‹sgn (a-b) ≃ 1›) this
    have : a-b ≄ 0 := mt sgn_zero.mp this
    have : a ≄ b := mt zero_diff_iff_eqv.mpr this
    have : Decidable (a ≃ b) := isFalse this
    exact this
  | AA.OneOfThree₁.third (_ : sgn (a-b) ≃ -1) =>
    have : (-1:ℤ) ≄ 0 := neg_one_neqv_zero
    have : sgn (a-b) ≄ 0 := AA.neqv_substL (Rel.symm ‹sgn (a-b) ≃ -1›) this
    have : a-b ≄ 0 := mt sgn_zero.mp this
    have : a ≄ b := mt zero_diff_iff_eqv.mpr this
    have : Decidable (a ≃ b) := isFalse this
    exact this

/--
Negation of subtraction swaps the operands.

**Property intuition**: The result of subtraction depends on the ordering of
the two operands. Negating the result is equivalent to reversing the operands'
order.

**Proof intuition**: Represent subtraction as addition; the negation operator
distributes to both operands. It undoes the negation of one operand, and adds
negation to the other. With negation swapped, the sum is still equivalent to
subtraction, but in the opposite order.
-/
theorem sub_neg_flip {a b : ℤ} : -(a - b) ≃ b - a := calc
  (-(a - b))   ≃ _ := AA.subst₁ sub_defn
  (-(a + -b))  ≃ _ := neg_compat_add
  (-a) + -(-b) ≃ _ := AA.substR neg_involutive
  (-a) + b     ≃ _ := AA.comm
  b + -a       ≃ _ := Rel.symm sub_defn
  b - a        ≃ _ := Rel.refl

end Lean4Axiomatic.Integer
