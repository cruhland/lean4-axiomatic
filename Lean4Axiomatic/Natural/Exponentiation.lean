import Lean4Axiomatic.Natural.Multiplication

/-!
# Natural number exponentiation
-/

namespace Lean4Axiomatic.Natural

open Logic (AP)
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
@[default_instance high]
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

variable [AA.Substitutive₂ (β := α) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)]

/--
Equivalent values can be substituted for the base (left operand) in an
exponentiation.

**Property intuition**: Exponentiation must satisfy this, to be considered a
function.

**Proof intuition**: Use induction on the exponent, since that's the operand
that has `zero` and `step` cases in the axioms. The base case and inductive
case both follow from expanding definitions and using substitution.
-/
theorem pow_substL {x₁ x₂ : α} {m : ℕ} : x₁ ≃ x₂ → x₁ ^ m ≃ x₂ ^ m := by
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
theorem pow_substR {x : α} {n₁ n₂ : ℕ} : n₁ ≃ n₂ → x ^ n₁ ≃ x ^ n₂ := by
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

/--
Exponents add when powers of the same base are multiplied.

**Property intuition**: Exponentiation is repeated multiplication; the exponent
is the count of repeats; counts are combined by adding.

**Proof intuition**: Induction and algebra.
-/
theorem pow_compatL_add
    [AA.Associative (α := α) (· * ·)] [AA.Commutative (α := α) (· * ·)]
    [AA.Identity (1:α) (· * ·)]
    {x : α} {n m : ℕ} : x^(n + m) ≃ x^n * x^m
    := by
  apply ind_on n
  case zero =>
    show x^(0 + m) ≃ x^(0:ℕ) * x^m
    calc
      _ ≃ x^(0 + m)     := Rel.refl
      _ ≃ x^m           := pow_substR AA.identL
      _ ≃ 1 * x^m       := Rel.symm AA.identL
      _ ≃ x^(0:ℕ) * x^m := AA.substL (Rel.symm pow_zero)
  case step =>
    intro n' (ih : x^(n' + m) ≃ x^n' * x^m)
    show x^(step n' + m) ≃ x^(step n') * x^m
    calc
      _ ≃ x^(step n' + m)   := Rel.refl
      _ ≃ x^(step (n' + m)) := pow_substR (Rel.symm AA.scompatL)
      _ ≃ x^(n' + m) * x    := pow_step
      _ ≃ (x^n' * x^m) * x  := AA.substL ih
      _ ≃ x^n' * (x^m * x)  := AA.assoc
      _ ≃ x^n' * (x * x^m)  := AA.substR AA.comm
      _ ≃ (x^n' * x) * x^m  := Rel.symm AA.assoc
      _ ≃ x^(step n') * x^m := AA.substL (Rel.symm pow_step)

/--
Left-associated powers can be flattened into a single power of the prouct of
the original exponents.

**Property intuition**: Having an expression with `n` repetitions of `x`, and
repeating that expression `m` times, gives `n * m` repetitions in total.

**Proof intuition**: Induction and algebra.
-/
theorem pow_flatten
    [AA.Associative (α := α) (· * ·)] [AA.Commutative (α := α) (· * ·)]
    [AA.Identity (1:α) (· * ·)]
    {x : α} {n m : ℕ} : (x^n)^m ≃ x^(n * m)
    := by
  apply ind_on m
  case zero =>
    show (x^n)^0 ≃ x^(n * 0)
    calc
      _ ≃ (x^n)^0   := Rel.refl
      _ ≃ 1         := pow_zero
      _ ≃ x^0       := Rel.symm pow_zero
      _ ≃ x^(n * 0) := pow_substR (Rel.symm mul_zero)
  case step =>
    intro m' (ih : (x^n)^m' ≃ x^(n * m'))
    show (x^n)^(step m') ≃ x^(n * step m')
    calc
      _ ≃ (x^n)^(step m')  := Rel.refl
      _ ≃ (x^n)^m' * x^n   := pow_step
      _ ≃ x^(n * m') * x^n := AA.substL ih
      _ ≃ x^(n * m' + n)   := Rel.symm pow_compatL_add
      _ ≃ x^(n * step m')  := pow_substR (Rel.symm mul_step)

/--
Exponents distribute over multiplication.

**Property intuition**: This is a simple regrouping of factors via the
associativity and commutativity of multiplication.

**Proof intuition**: Induction and algebra.
-/
theorem pow_distribR_mul
    [AA.Associative (α := α) (· * ·)] [AA.Commutative (α := α) (· * ·)]
    [AA.Identity (1:α) (· * ·)]
    {x y : α} {n : ℕ} : (x * y)^n ≃ x^n * y^n
    := by
  apply ind_on n
  case zero =>
    show (x * y)^0 ≃ x^0 * y^0
    calc
      _ ≃ (x * y)^0 := Rel.refl
      _ ≃ 1         := pow_zero
      _ ≃ 1 * 1     := Rel.symm AA.identR
      _ ≃ x^0 * 1   := AA.substL (Rel.symm pow_zero)
      _ ≃ x^0 * y^0 := AA.substR (Rel.symm pow_zero)
  case step =>
    intro n' (ih : (x * y)^n' ≃ x^n' * y^n')
    show (x * y)^(step n') ≃ x^(step n') * y^(step n')
    calc
      _ ≃ (x * y)^(step n')         := Rel.refl
      _ ≃ (x * y)^n' * (x * y)      := pow_step
      _ ≃ (x^n' * y^n') * (x * y)   := AA.substL ih
      _ ≃ (x^n' * x) * (y^n' * y)   := AA.expr_xxfxxff_lr_swap_rl
      _ ≃ x^(step n') * (y^n' * y)  := AA.substL (Rel.symm pow_step)
      _ ≃ x^(step n') * y^(step n') := AA.substR (Rel.symm pow_step)

/--
If an exponentiation to a natural number evaluates to zero, then the base must
be zero and the exponent must be nonzero.

**Property and proof intuition**: The only products that evaluate to zero are
those that have zero as a factor (if the zero-product property holds); thus the
base must be zero. By definition, exponentiation gives one if the exponent is
zero; thus it must be nonzero in this case.
-/
theorem pow_inputs_for_output_zero
    [OfNat α 0] [AP ((1:α) ≄ 0)] [AA.ZeroProduct (α := α) (· * ·)]
    {x : α} {n : ℕ} : x^n ≃ 0 → x ≃ 0 ∧ n ≄ 0
    := by
  apply ind_on (motive := λ m => x^m ≃ 0 → x ≃ 0 ∧ m ≄ 0) n
  case zero =>
    intro (_ : x^(0:ℕ) ≃ 0)
    show x ≃ 0 ∧ 0 ≄ 0
    have : (1:α) ≃ 0 := calc
      _ ≃ 1   := Rel.refl
      _ ≃ x^0 := Rel.symm pow_zero
      _ ≃ 0   := ‹x^(0:ℕ) ≃ 0›
    exact absurd ‹(1:α) ≃ 0› ‹AP ((1:α) ≄ 0)›.ev
  case step =>
    intro (n' : ℕ) (ih : x^n' ≃ 0 → x ≃ 0 ∧ n' ≄ 0) (_ : x^(step n') ≃ 0)
    show x ≃ 0 ∧ step n' ≄ 0
    have : x^n' * x ≃ 0 := AA.eqv_substL pow_step ‹x^(step n') ≃ 0›
    have : x^n' ≃ 0 ∨ x ≃ 0 := AA.zero_prod this
    have : x ≃ 0 :=
      match this with
      | Or.inl (_ : x^n' ≃ 0) => (ih ‹x^n' ≃ 0›).left
      | Or.inr (_ : x ≃ 0) => ‹x ≃ 0›
    have : step n' ≄ 0 := step_neqv_zero
    exact And.intro ‹x ≃ 0› ‹step n' ≄ 0›

/--
Describes the exact conditions on exponentiation's inputs that cause it to
output the value zero.

**Property intuition**: A product is zero only when at least one factor is
zero. And the empty product (raising to the zero power) is `1`.

**Proof intuition**: See `pow_inputs_for_output_zero` for the forward
direction. In the reverse direction, the resulting product must have at least
one factor (because the exponent is nonzero), and since that factor is zero,
the result is zero by absorption.
-/
theorem pow_eqv_zero
    [OfNat α 0] [AP ((1:α) ≄ 0)] [AA.ZeroProduct (α := α) (· * ·)]
    [AA.Absorbing (0:α) (· * ·)]
    {x : α} {n : ℕ} : x^n ≃ 0 ↔ x ≃ 0 ∧ n ≄ 0
    := by
  apply Iff.intro
  case mp =>
    show x^n ≃ 0 → x ≃ 0 ∧ n ≄ 0
    exact pow_inputs_for_output_zero
  case mpr =>
    intro (And.intro (_ : x ≃ 0) (_ : n ≄ 0))
    show x^n ≃ 0
    have : Positive n := Signed.positive_defn.mpr ‹n ≄ 0›
    have (Exists.intro (n' : ℕ) (_ : step n' ≃ n)) := positive_step this
    calc
      _ ≃ x^n         := Rel.refl
      _ ≃ x^(step n') := pow_substR (Rel.symm ‹step n' ≃ n›)
      _ ≃ x^n' * x    := pow_step
      _ ≃ x^n' * 0    := AA.substR ‹x ≃ 0›
      _ ≃ 0           := AA.absorbR

/--
Raising a nonzero number to any natural number power always gives a nonzero
result.

**Property intuition**: The empty product is `1` (raising to the zero power),
and any product of nonzero numbers is always nonzero (higher powers).

**Proof intuition**: Follows from `pow_inputs_for_output_zero` by logic alone.
-/
theorem pow_preserves_nonzero_base
    [OfNat α 0] [AP ((1:α) ≄ 0)] [AA.ZeroProduct (α := α) (· * ·)]
    {x : α} {n : ℕ} : x ≄ 0 → x^n ≄ 0
    := by
  intro (_ : x ≄ 0)
  show x^n ≄ 0
  have : ¬(x ≃ 0 ∧ n ≄ 0) := by
    intro (And.intro (_ : x ≃ 0) (_ : n ≄ 0))
    show False
    exact absurd ‹x ≃ 0› ‹x ≄ 0›
  have : x^n ≄ 0 := mt pow_inputs_for_output_zero this
  exact this

/-- TODO -/
instance pow_preserves_nonzero_base_inst
    [OfNat α 0] [AP ((1:α) ≄ 0)] [AA.ZeroProduct (α := α) (· * ·)]
    {x : α} {n : ℕ} [AP (x ≄ 0)] : AP (x^n ≄ 0)
    :=
  ‹AP (x ≄ 0)›.map pow_preserves_nonzero_base

end general

end Lean4Axiomatic.Natural
