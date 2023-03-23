import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Rational.Addition

/-! # Rational numbers: multiplication -/

namespace Lean4Axiomatic.Rational

/-! ## Axioms -/

/-- Operations pertaining to rational number multiplication. -/
class Multiplication.Ops (ℚ : Type) :=
  /-- Multiplication of rational numbers. -/
  mul : ℚ → ℚ → ℚ

export Multiplication.Ops (mul)

/-- Enables the use of the `· * ·` operator for multiplication. -/
instance mul_op_inst {ℚ : Type} [Multiplication.Ops ℚ] : Mul ℚ := {
  mul := mul
}

/-- Properties of rational number multiplication. -/
class Multiplication.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Ops ℚ]
    :=
  /-- Multiplication respects equivalence over its left operand. -/
  mul_substL {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → p₁ * q ≃ p₂ * q

  /-- Multiplication respects equivalence over its right operand. -/
  mul_substR {p₁ p₂ q : ℚ} : p₁ ≃ p₂ → q * p₁ ≃ q * p₂

  /-- Multiplication is consistent with its integer equivalent. -/
  mul_compat_from_integer {a b : ℤ} : ((a * b : ℤ) : ℚ) ≃ (a : ℚ) * (b : ℚ)

  /-- Multiplication is commutative. -/
  mul_comm {p q : ℚ} : p * q ≃ q * p

  /-- Multiplication is associative. -/
  mul_assoc {p q r : ℚ} : (p * q) * r ≃ p * (q * r)

  /-- One is a left multiplicative identity. -/
  mul_identL {p : ℚ} : 1 * p ≃ p

  /-- One is a right multiplicative identity. -/
  mul_identR {p : ℚ} : p * 1 ≃ p

  /-- Multiplication on the left distributes over addition. -/
  mul_distribL {p q r : ℚ} : p * (q + r) ≃ p * q + p * r

  /-- Multiplication on the right distributes over addition. -/
  mul_distribR {p q r : ℚ} : (q + r) * p ≃ q * p + r * p

export Multiplication.Props (
  mul_assoc mul_comm mul_compat_from_integer mul_distribL mul_distribR
  mul_identL mul_identR mul_substL mul_substR
)

/-- All axioms of multiplication for rational numbers. -/
class Multiplication
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ]
    :=
  toOps : Multiplication.Ops ℚ
  toProps : Multiplication.Props ℚ

attribute [instance] Multiplication.toOps
attribute [instance] Multiplication.toProps

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]

/-- Enables the use of `AA.substL`, `AA.substR`, etc. for multiplication. -/
instance mul_subst_inst
    : AA.Substitutive₂ (α := ℚ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := { subst₂ := λ (_ : True) => mul_substL }
  substitutiveR := { subst₂ := λ (_ : True) => mul_substR }
}

/-- Enables the use of `AA.comm` for commutativity of multiplication. -/
instance mul_comm_inst : AA.Commutative (α := ℚ) (· * ·) := {
  comm := mul_comm
}

/-- Enables the use of `AA.assoc` for associativity of multiplication. -/
instance mul_assoc_inst : AA.Associative (α := ℚ) (· * ·) := {
  assoc := mul_assoc
}

/--
Holds for the rational numbers that are square roots of unity, i.e. that result
in `1` when squared.

See `Integer.Sqrt1` for details on why this is a useful predicate.
-/
class inductive Sqrt1 (p : ℚ) : Prop :=
| /--
  Create `Sqrt1` for the rational equivalent of an integer square root of
  unity.
  -/
  from_integer_intro (a : ℤ) (sqrt1 : Integer.Sqrt1 a) (eqv : p ≃ (a : ℚ))

/-- Alternative to `Sqrt1.from_integer_intro` that infers more arguments. -/
def Sqrt1.from_integer
    {a : ℤ} {p : ℚ} [Integer.Sqrt1 a] : p ≃ (a : ℚ) → Sqrt1 p
    :=
  from_integer_intro a ‹Integer.Sqrt1 a›

/--
The defining property of square roots of unity.

**Proof intuition**: Expand the definition of `Sqrt1` to obtain the underlying
integer. Then show the property is preserved by conversion to rational numbers.
-/
theorem Sqrt1.elim {p : ℚ} : Sqrt1 p → p * p ≃ 1 := by
  intro (_ : Sqrt1 p)
  show p * p ≃ 1
  have (Sqrt1.from_integer_intro (a : ℤ) (_ : Integer.Sqrt1 a) eqv) :=
    ‹Sqrt1 p›
  have : p ≃ (a : ℚ) := eqv
  have : p * p ≃ 1 := calc
    p * p             ≃ _ := mul_substL ‹p ≃ (a : ℚ)›
    (a : ℚ) * p       ≃ _ := mul_substR ‹p ≃ (a : ℚ)›
    (a : ℚ) * (a : ℚ) ≃ _ := eqv_symm mul_compat_from_integer
    ((a * a : ℤ) : ℚ) ≃ _ := from_integer_subst ‹Integer.Sqrt1 a›.elim
    (1 : ℚ)           ≃ _ := eqv_refl
    1                 ≃ _ := eqv_refl
  exact this

/--
The `Sqrt1` predicate respects equivalence of rational numbers.

**Property intuition**: This must hold for `Sqrt1` to be a valid predicate.

**Proof intuition**: Expand the definition of `Sqrt1`; the result follows by
substitution on the underlying equivalence.
-/
theorem sqrt1_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → Sqrt1 p₁ → Sqrt1 p₂ := by
  intro (_ : p₁ ≃ p₂) (_ : Sqrt1 p₁)
  show Sqrt1 p₂
  have (Sqrt1.from_integer_intro (a : ℤ) (_ : Integer.Sqrt1 a) eqv) :=
    ‹Sqrt1 p₁›
  have : p₁ ≃ (a : ℚ) := eqv
  have : p₂ ≃ (a : ℚ) := AA.substLFn ‹p₁ ≃ p₂› this
  have : Sqrt1 p₂ := Sqrt1.from_integer_intro a ‹Integer.Sqrt1 a› this
  exact this

/--
An integer square root of unity keeps that designation when converted to a
rational number.

**Property intuition**: Multiplication is preserved by integer conversion, and
the square root of unity property is defined in terms of multiplication, so we
expect it to be preserved as well.

**Proof intuition**: `Sqrt1` for rationals already delegates to the definition
for integers; expand it and use that connection.
-/
theorem from_integer_preserves_sqrt1
    {a : ℤ} : Sqrt1 (a : ℚ) ↔ Integer.Sqrt1 a := by
  apply Iff.intro
  case mp =>
    intro (_ : Sqrt1 (a : ℚ))
    show Integer.Sqrt1 a
    have (Sqrt1.from_integer_intro (b : ℤ) (_ : Integer.Sqrt1 b) eqv) :=
      ‹Sqrt1 (a : ℚ)›
    have : (b : ℚ) ≃ (a : ℚ) := eqv_symm eqv
    have : b ≃ a := from_integer_inject this
    have : Integer.Sqrt1 a := Integer.sqrt1_subst this ‹Integer.Sqrt1 b›
    exact this
  case mpr =>
    intro (_ : Integer.Sqrt1 a)
    show Sqrt1 (a : ℚ)
    exact Sqrt1.from_integer eqv_refl

/--
The rational number `1` is a square root of unity.

**Property and proof intuition**: This is a trivial corollary of the proof that
integer square roots of unity are also rational square roots of unity.
-/
instance sqrt1_one : Sqrt1 (1 : ℚ) :=
  from_integer_preserves_sqrt1.mpr Integer.sqrt1_one

end Lean4Axiomatic.Rational
