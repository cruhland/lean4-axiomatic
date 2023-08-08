import Lean4Axiomatic.Natural.Multiplication

/-!
# Natural number exponentiation
-/

namespace Lean4Axiomatic.Natural

open Relation.Equivalence (EqvOp)
open Signed (Positive)

/-!
## Axioms
-/

/-- Operations for raising numeric values to natural number powers. -/
class Exponentiation.Ops (α : Type) (ℕ : outParam Type) :=
  /-- Exponentiation to a natural number power. -/
  _pow : α → ℕ → α

/--
Enables the use of the `· ^ ·` operator for exponentiation.

Has an explicit priority so it is chosen before the standard library's
`Pow Nat Nat` instance.
-/
instance (priority := default+1) pow_inst
    {α ℕ : Type} [Exponentiation.Ops α ℕ] : Pow α ℕ
    := {
  pow := Exponentiation.Ops._pow
}

/-- Properties of exponentiation to a natural number. -/
class Exponentiation.Props
    {α : Type} {ℕ : outParam Type} (mul : outParam (α → α → α))
    [Core ℕ] [Addition ℕ] [Multiplication ℕ] [EqvOp α] [OfNat α 1] [Ops α ℕ]
    :=
  /-- Any number raised to the power zero, is one. -/
  pow_zero {x : α} : x ^ (0:ℕ) ≃ 1

  /-- Adding one to the exponent multiplies the result by the base. -/
  pow_step {x : α} {n : ℕ} : x ^ step n ≃ mul (x ^ n) x

export Exponentiation.Props (pow_step pow_zero)

/-- All exponentiation axioms. -/
class Exponentiation
    (ℕ : semiOutParam Type) {α : Type} (mul : semiOutParam (α → α → α))
    [Core ℕ] [Addition ℕ] [Multiplication ℕ] [EqvOp α] [OfNat α 1]
    :=
  toOps : Exponentiation.Ops α ℕ
  toProps : Exponentiation.Props mul

attribute [instance] Exponentiation.toOps
attribute [instance] Exponentiation.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type}
    [Core ℕ] [Induction.{0} ℕ] [Addition ℕ] [Sign ℕ] [Multiplication ℕ]

section general

/-! ### General properties for any base type -/

variable
  {α : Type} {mul : α → α → α} [EqvOp α] [OfNat α 1] [Exponentiation ℕ mul]

/-- Enables the use of `· * ·` syntax for `α`'s multiplication function. -/
local instance mul_inst [Exponentiation ℕ mul] : Mul α := {
  mul := mul
}

/--
Equivalent values can be substituted for the base (left operand) in an
exponentiation.

**Property intuition**: Exponentiation must satisfy this, to be considered a
function.

**Proof intuition**: Use induction on the exponent, since that's the operand
that has `zero` and `step` cases in the axioms. The base case and inductive
case both follow from expanding definitions and using substitution.
-/
theorem pow_substL
    {x₁ x₂ : α} [AA.Substitutive₂ (β := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)]
    {m : ℕ} : x₁ ≃ x₂ → x₁ ^ m ≃ x₂ ^ m
    := by
  intro (_ : x₁ ≃ x₂)
  show x₁ ^ m ≃ x₂ ^ m
  apply ind_on (motive := λ y => x₁ ^ y ≃ x₂ ^ y) m
  case zero =>
    show x₁ ^ 0 ≃ x₂ ^ 0
    calc
      _ ≃ x₁ ^ 0 := Rel.refl
      _ ≃ 1      := pow_zero
      _ ≃ x₂ ^ 0 := Rel.symm pow_zero
  case step =>
    intro (m' : ℕ) (ih : x₁ ^ m' ≃ x₂ ^ m')
    show x₁ ^ step m' ≃ x₂ ^ step m'
    calc
      _ ≃ x₁ ^ step m' := Rel.refl
      _ ≃ x₁ ^ m' * x₁ := pow_step
      _ ≃ x₂ ^ m' * x₁ := AA.substL ih
      _ ≃ x₂ ^ m' * x₂ := AA.substR ‹x₁ ≃ x₂›
      _ ≃ x₂ ^ step m' := Rel.symm pow_step

/--
Equivalent values can be substituted for the exponent (right operand) in an
exponentiation.

**Property intuition**: Exponentiation must satisfy this, to be considered a
function.

**Proof intuition**: Use induction on the exponent, since that's the operand
that has `zero` and `step` cases in the axioms. It's a bit more difficult than
the left-hand version, because we have two exponent values: `n₁` and `n₂`. Thus
we need to do a case-split on `n₂` within the base case and inductive case for
`n₁`. The `zero, zero` case is a trivial equivalence; the `zero, step` and
`step, zero` cases are contradictions. That leaves the interesting `step, step`
case, which expands definitions, then uses substitution and the inductive
hypothesis.
-/
theorem pow_substR
    {x : α} [AA.Substitutive₂ (β := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)]
    {n₁ n₂ : ℕ} : n₁ ≃ n₂ → x ^ n₁ ≃ x ^ n₂
    := by
  apply ind_on (motive := λ k => ∀ {j}, k ≃ j → x ^ k ≃ x ^ j) n₁
  case zero =>
    intro (n₂ : ℕ)
    show 0 ≃ n₂ → x ^ 0 ≃ x ^ n₂
    apply cases_on (motive := λ j => 0 ≃ j → x ^ 0 ≃ x ^ j) n₂
    case zero =>
      intro (_ : (0 : ℕ) ≃ 0)
      show x ^ 0 ≃ x ^ 0
      exact Rel.refl
    case step =>
      intro (n₂' : ℕ) (_ : 0 ≃ step n₂')
      show x ^ 0 ≃ x ^ step n₂'
      exact absurd ‹0 ≃ step n₂'› (Rel.symm step_neqv_zero)
  case step =>
    intro (n₁' : ℕ) (ih : ∀ {j}, n₁' ≃ j → x ^ n₁' ≃ x ^ j) (n₂ : ℕ)
    show step n₁' ≃ n₂ → x ^ step n₁' ≃ x ^ n₂
    apply cases_on (motive := λ j => step n₁' ≃ j → x ^ step n₁' ≃ x ^ j) n₂
    case zero =>
      intro (_ : step n₁' ≃ 0)
      show x ^ step n₁' ≃ x ^ 0
      exact absurd ‹step n₁' ≃ 0› step_neqv_zero
    case step =>
      intro (n₂' : ℕ) (_ : step n₁' ≃ step n₂')
      show x ^ step n₁' ≃ x ^ step n₂'
      have : n₁' ≃ n₂' := AA.inject ‹step n₁' ≃ step n₂'›
      calc
        _ ≃ x ^ step n₁' := Rel.refl
        _ ≃ x ^ n₁' * x  := pow_step
        _ ≃ x ^ n₂' * x  := AA.substL (ih ‹n₁' ≃ n₂'›)
        _ ≃ x ^ step n₂' := Rel.symm pow_step

end general

/-! ### Specific properties for a natural number base -/

variable [Exponentiation ℕ (α := ℕ) (· * ·)]

/--
Exponentiation of natural numbers can give a zero result only when the base is
zero and the exponent is nonzero.

**Property intuition**: A product of natural numbers is zero only when at least
one factor is zero. And the empty product (raising to the zero power) is `1`.

**Proof intuition**: By induction on `m` in the forwards direction. The base
case follows by contradiction; anything to the zero power is one, not zero. In
the inductive case, `n ^ step m'` expands into `n ^ m' * n`, implying that
either `n ^ m' ≃ 0` or `n ≃ 0`. The former case becomes the latter case after
applying the induction hypothesis. In the reverse direction, expand definitions
until `n ^ m' * n` is reached. Since `n ≃ 0`, the entire expression is zero.
-/
theorem pow_eqv_zero {n m : ℕ} : n ^ m ≃ 0 ↔ n ≃ 0 ∧ m ≄ 0 := by
  apply Iff.intro
  case mp =>
    apply ind_on (motive := λ x => n ^ x ≃ 0 → n ≃ 0 ∧ x ≄ 0) m
    case zero =>
      intro (_ : n ^ 0 ≃ 0)
      show n ≃ 0 ∧ 0 ≄ 0
      have : step 0 ≃ 0 := calc
        _ ≃ step 0 := Rel.refl
        _ ≃ 1      := Rel.symm literal_step
        _ ≃ n ^ 0  := Rel.symm pow_zero
        _ ≃ 0      := ‹n ^ 0 ≃ 0›
      exact absurd ‹step 0 ≃ 0› step_neqv_zero
    case step =>
      intro (m' : ℕ) (ih : n ^ m' ≃ 0 → n ≃ 0 ∧ m' ≄ 0) (_ : n ^ step m' ≃ 0)
      show n ≃ 0 ∧ step m' ≄ 0
      have : n ^ m' * n ≃ 0 := AA.eqv_substL pow_step ‹n ^ step m' ≃ 0›
      have : n ^ m' ≃ 0 ∨ n ≃ 0 := mul_split_zero.mp this
      have : n ≃ 0 :=
        match this with
        | Or.inl (_ : n ^ m' ≃ 0) => (ih ‹n ^ m' ≃ 0›).left
        | Or.inr (_ : n ≃ 0) => ‹n ≃ 0›
      have : step m' ≄ 0 := step_neqv_zero
      exact And.intro ‹n ≃ 0› ‹step m' ≄ 0›
  case mpr =>
    intro (And.intro (_ : n ≃ 0) (_ : m ≄ 0))
    show n ^ m ≃ 0
    have : Positive m := Signed.positive_defn.mpr ‹m ≄ 0›
    have (Exists.intro (m' : ℕ) (_ : step m' ≃ m)) := positive_step this
    calc
      _ ≃ n ^ m       := Rel.refl
      _ ≃ n ^ step m' := pow_substR (Rel.symm ‹step m' ≃ m›)
      _ ≃ n ^ m' * n  := pow_step
      _ ≃ n ^ m' * 0  := AA.substR ‹n ≃ 0›
      _ ≃ 0           := AA.absorbR

/--
Raising a nonzero natural number to any natural number power always gives a
nonzero result.

**Property intuition**: The empty product is `1` (raising to the zero power),
and any product of nonzero numbers is always nonzero (higher powers).

**Proof intuition**: Follows from `pow_eqv_zero` by logic alone.
-/
theorem pow_preserves_nonzero_base {n m : ℕ} : n ≄ 0 → n ^ m ≄ 0 := by
  intro (_ : n ≄ 0)
  show n ^ m ≄ 0
  have : ¬(n ≃ 0 ∧ m ≄ 0) := by
    intro (And.intro (_ : n ≃ 0) (_ : m ≄ 0))
    show False
    exact absurd ‹n ≃ 0› ‹n ≄ 0›
  have : n ^ m ≄ 0 := mt pow_eqv_zero.mp this
  exact this

end Lean4Axiomatic.Natural
