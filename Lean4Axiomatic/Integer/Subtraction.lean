import Lean4Axiomatic.Integer.Sign

/-! # Integer subtraction -/

namespace Lean4Axiomatic.Integer

/-! ## Axioms -/

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

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]
    [Negation ℤ] [Sign ℤ] [Subtraction ℤ]

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

/--
Subtraction with the additive identity on the left negates the right operand.

**Property and proof intuition**: By definition of subtraction and the additive
identity.
-/
theorem sub_identL {a : ℤ} : 0 - a ≃ -a := calc
  _ = 0 - a  := rfl
  _ ≃ 0 + -a := sub_defn
  _ ≃ -a     := AA.identL

/--
Subtraction with the additive identity on the right gives the left operand.

**Property and proof intuition**: By definition of subtraction and the additive
identity.
-/
theorem sub_identR {a : ℤ} : a - 0 ≃ a := calc
  _ = a - 0        := rfl
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

/-- TODO -/
theorem sub_assoc_addL {a b c : ℤ} : (a + b) - c ≃ a + (b - c) := calc
  _ = (a + b) - c  := rfl
  _ ≃ (a + b) + -c := sub_defn
  _ ≃ a + (b + -c) := AA.assoc
  _ ≃ a + (b - c)  := AA.substR (Rel.symm sub_defn)

/-- TODO -/
theorem sub_assoc_addR {a b c : ℤ} : (a - b) + c ≃ a + (c - b) := calc
  _ = (a - b) + c  := rfl
  _ ≃ (a + -b) + c := AA.substL sub_defn
  _ ≃ a + (-b + c) := AA.assoc
  _ ≃ a + (c + -b) := AA.substR AA.comm
  _ ≃ a + (c - b)  := AA.substR (Rel.symm sub_defn)

/-- TODO -/
theorem subR_moveR_addR {a b c : ℤ} : a - b ≃ c ↔ a ≃ c + b := calc
  _ ↔       a - b ≃ c     := Iff.rfl
  _ ↔ (a - b) + b ≃ c + b := add_bijectR
  _ ↔ a + (b - b) ≃ c + b := AA.eqv_substL_iff sub_assoc_addR
  _ ↔       a + 0 ≃ c + b := AA.eqv_substL_iff (AA.substR sub_same)
  _ ↔           a ≃ c + b := AA.eqv_substL_iff AA.identR

/--
The right-hand operand of subtraction can be moved to the left-hand operand of
addition on the other side of an equivalence.

**Property intuition**: This is a very common technique in algebra.

**Proof intuition**: TODO
-/
theorem subR_moveR_addL {a b c : ℤ} : a - b ≃ c ↔ a ≃ b + c := calc
  _ ↔ a - b ≃ c     := Iff.rfl
  _ ↔     a ≃ c + b := subR_moveR_addR
  _ ↔     a ≃ b + c := AA.eqv_substR_iff AA.comm

/-- TODO -/
theorem subR_moveL_addR {a b c : ℤ} : a ≃ b - c ↔ a + c ≃ b := calc
  _ ↔     a ≃ b - c := Iff.rfl
  _ ↔ b - c ≃ a     := Fn.swap
  _ ↔     b ≃ a + c := subR_moveR_addR
  _ ↔ a + c ≃ b     := Fn.swap

/-- TODO -/
theorem subR_moveL_addL {a b c : ℤ} : a ≃ b - c ↔ c + a ≃ b := calc
  _ ↔     a ≃ b - c := Iff.rfl
  _ ↔ a + c ≃ b     := subR_moveL_addR
  _ ↔ c + a ≃ b     := AA.eqv_substL_iff AA.comm

/-- TODO -/
theorem sub_swap_add {a b c d : ℤ} : a - b ≃ c - d ↔ a + d ≃ c + b := calc
  _ ↔ a - b ≃ c - d       := Iff.rfl
  _ ↔     a ≃ (c - d) + b := subR_moveR_addR
  _ ↔     a ≃ c + (b - d) := AA.eqv_substR_iff sub_assoc_addR
  _ ↔     a ≃ (c + b) - d := AA.eqv_substR_iff (Rel.symm sub_assoc_addL)
  _ ↔ a + d ≃ c + b       := subR_moveL_addR

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
