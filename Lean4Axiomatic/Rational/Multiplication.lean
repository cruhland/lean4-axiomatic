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
class Sqrt1 (p : ℚ) : Prop :=
  /-- The defining property of square roots of unity. -/
  elim : p * p ≃ 1

/--
The `Sqrt1` predicate respects equivalence of rational numbers.

**Property intuition**: This must hold for `Sqrt1` to be a valid predicate.

**Proof intuition**: Expand the definition of `Sqrt1`; the result follows by
substitution on multiplication.
-/
theorem sqrt1_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → Sqrt1 p₁ → Sqrt1 p₂ := by
  intro (_ : p₁ ≃ p₂) (_ : Sqrt1 p₁)
  show Sqrt1 p₂
  have : p₂ * p₂ ≃ 1 := calc
    p₂ * p₂ ≃ _ := mul_substL (eqv_symm ‹p₁ ≃ p₂›)
    p₁ * p₂ ≃ _ := mul_substR (eqv_symm ‹p₁ ≃ p₂›)
    p₁ * p₁ ≃ _ := ‹Sqrt1 p₁›.elim
    1       ≃ _ := eqv_refl
  have : Sqrt1 p₂ := Sqrt1.mk this
  exact this

/--
An integer square root of unity keeps that designation when converted to a
rational number.

**Property intuition**: Multiplication is preserved by integer conversion, and
the square root of unity property is defined in terms of multiplication, so we
expect it to be preserved as well.

**Proof intuition**: Use integer conversion's substitutive, injective, and
multiplicative compatibility properties to show that the underlying algebraic
representations of square roots of unity are equivalent.
-/
theorem from_integer_preserves_sqrt1
    {a : ℤ} : Sqrt1 (a : ℚ) ↔ Integer.Sqrt1 a := by
  apply Iff.intro
  case mp =>
    intro (_ : Sqrt1 (a : ℚ))
    show Integer.Sqrt1 a
    have : ((a * a : ℤ) : ℚ) ≃ ((1 : ℤ) : ℚ) := calc
      ((a * a : ℤ) : ℚ) ≃ _ := mul_compat_from_integer
      (a : ℚ) * (a : ℚ) ≃ _ := ‹Sqrt1 (a : ℚ)›.elim
      ((1 : ℤ) : ℚ)     ≃ _ := eqv_refl
    have : a * a ≃ 1 := from_integer_inject this
    have : Integer.Sqrt1 a := Integer.Sqrt1.mk this
    exact this
  case mpr =>
    intro (_ : Integer.Sqrt1 a)
    show Sqrt1 (a : ℚ)
    have : (a : ℚ) * (a : ℚ) ≃ 1 := calc
      (a : ℚ) * (a : ℚ) ≃ _ := eqv_symm mul_compat_from_integer
      ((a * a : ℤ) : ℚ) ≃ _ := from_integer_subst ‹Integer.Sqrt1 a›.elim
      (1 : ℚ)           ≃ _ := eqv_refl
    have : Sqrt1 (a : ℚ) := Sqrt1.mk this
    exact this

/--
The rational number `1` is a square root of unity.

**Property and proof intuition**: This is a trivial corollary of the proof that
integer square roots of unity are also rational square roots of unity.
-/
instance sqrt1_one : Sqrt1 (1 : ℚ) :=
  from_integer_preserves_sqrt1.mpr Integer.sqrt1_one

end Lean4Axiomatic.Rational
