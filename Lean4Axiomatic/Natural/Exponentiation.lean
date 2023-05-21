import Lean4Axiomatic.Natural.Multiplication

/-!
# Natural number exponentiation
-/

namespace Lean4Axiomatic.Natural

open Signed (Positive)

/-!
## Axioms
-/

/--
Definition of exponentiation, and properties that it must satisfy.

All other properties of exponentiation can be derived from these.
-/
class Exponentiation (ℕ : Type) [Core ℕ] [Addition ℕ] [Multiplication ℕ] :=
  /-- Definition of and syntax for exponentiation. -/
  powOp : Pow ℕ ℕ

  /-- Raising a natural number to the power zero always gives one. -/
  pow_zero {n : ℕ} : n ^ 0 ≃ 1

  /--
  Each increment of the exponent puts another factor of the base on the result.
  -/
  pow_step {n m : ℕ} : n ^ step m ≃ n ^ m * n

attribute [instance] Exponentiation.powOp

export Exponentiation (powOp pow_step pow_zero)

/-! ## Derived properties -/

variable
  {ℕ : Type}
  [Core ℕ] [Axioms ℕ] [Addition ℕ] [Sign ℕ] [Multiplication ℕ]
  [Exponentiation ℕ]

/--
Equivalent values can be substituted for the base (left operand) in an
exponentiation.

**Property intuition**: Exponentiation must satisfy this, to be considered a
function.

**Proof intuition**: Use induction on the exponent, since that's the operand
that has `zero` and `step` cases in the axioms. The base case and inductive
case both follow from expanding definitions and using substitution.
-/
theorem pow_substL {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ ^ m ≃ n₂ ^ m := by
  intro (_ : n₁ ≃ n₂)
  show n₁ ^ m ≃ n₂ ^ m
  apply ind_on (motive := λ x => n₁ ^ x ≃ n₂ ^ x) m
  case zero =>
    show n₁ ^ 0 ≃ n₂ ^ 0
    calc
      _ ≃ n₁ ^ 0 := Rel.refl
      _ ≃ 1      := pow_zero
      _ ≃ n₂ ^ 0 := Rel.symm pow_zero
  case step =>
    intro (m' : ℕ) (ih : n₁ ^ m' ≃ n₂ ^ m')
    show n₁ ^ step m' ≃ n₂ ^ step m'
    calc
      _ ≃ n₁ ^ step m' := Rel.refl
      _ ≃ n₁ ^ m' * n₁ := pow_step
      _ ≃ n₂ ^ m' * n₁ := AA.substL ih
      _ ≃ n₂ ^ m' * n₂ := AA.substR ‹n₁ ≃ n₂›
      _ ≃ n₂ ^ step m' := Rel.symm pow_step

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
theorem pow_substR {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m ^ n₁ ≃ m ^ n₂ := by
  apply ind_on (motive := λ x => ∀ {y}, x ≃ y → m ^ x ≃ m ^ y) n₁
  case zero =>
    intro (n₂ : ℕ)
    show 0 ≃ n₂ → m ^ 0 ≃ m ^ n₂
    apply cases_on (motive := λ y => 0 ≃ y → m ^ 0 ≃ m ^ y) n₂
    case zero =>
      intro (_ : (0 : ℕ) ≃ 0)
      show m ^ 0 ≃ m ^ 0
      exact Rel.refl
    case step =>
      intro (n₂' : ℕ) (_ : 0 ≃ step n₂')
      show m ^ 0 ≃ m ^ step n₂'
      exact absurd ‹0 ≃ step n₂'› (Rel.symm step_neqv_zero)
  case step =>
    intro (n₁' : ℕ) (ih : ∀ {y}, n₁' ≃ y → m ^ n₁' ≃ m ^ y) (n₂ : ℕ)
    show step n₁' ≃ n₂ → m ^ step n₁' ≃ m ^ n₂
    apply cases_on (motive := λ y => step n₁' ≃ y → m ^ step n₁' ≃ m ^ y) n₂
    case zero =>
      intro (_ : step n₁' ≃ 0)
      show m ^ step n₁' ≃ m ^ 0
      exact absurd ‹step n₁' ≃ 0› step_neqv_zero
    case step =>
      intro (n₂' : ℕ) (_ : step n₁' ≃ step n₂')
      show m ^ step n₁' ≃ m ^ step n₂'
      have : n₁' ≃ n₂' := AA.inject ‹step n₁' ≃ step n₂'›
      calc
        _ ≃ m ^ step n₁' := Rel.refl
        _ ≃ m ^ n₁' * m  := pow_step
        _ ≃ m ^ n₂' * m  := AA.substL (ih ‹n₁' ≃ n₂'›)
        _ ≃ m ^ step n₂' := Rel.symm pow_step

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
