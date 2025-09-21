import Lean4Axiomatic.Rational.Addition
import Lean4Axiomatic.Rational.Impl.Fraction.Core

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Signed (Positive)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Fraction addition -/

/--
Addition of fractions.

Uses naive fraction addition, and the proof that naive fraction addition always
results in a positive denominator if the input denominators are positive.
-/
def add (p q : Fraction ℤ) : Fraction ℤ :=
  let sum := p.naive + q.naive
  have : Positive p.denominator := p.denominator_positive.ev
  have : Positive q.denominator := q.denominator_positive.ev
  have : Positive sum.denominator :=
    Naive.add_preserves_positive_denominators
      ‹Positive p.denominator›
      ‹Positive q.denominator›
  from_naive sum ‹Positive sum.denominator›

instance addition_ops : Addition.Ops (Fraction ℤ) := {
  add := add
}

/--
Addition of integer fractions is consistent with its equivalent on integers.

**Property intuition**: This must be true if we want integers to be represented
as integer fractions.

**Proof intuition**: Expand the definition of addition and use integer algebra
on the numerator and denominator.
-/
theorem add_compat_from_integer
    {a b : ℤ} : from_integer (a + b) ≃ from_integer a + from_integer b
    := eqv_symm $ calc
  _ = from_integer a + from_integer b := rfl
  _ = a//1 + b//1                     := rfl
  _ = (a * 1 + 1 * b)//(1 * 1)        := rfl
  _ ≃ (a + 1 * b)//(1 * 1)            := by srw [Integer.mul_identR]
  _ ≃ (a + b)//(1 * 1)                := by srw [Integer.mul_identL]
  _ ≃ (a + b)//1                      := by srw [Integer.mul_identR]
  _ = from_integer (a + b)            := rfl

/--
Addition of integer fractions is commutative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Expand the definition of addition and use integer algebra
on the numerator and denominator.
-/
theorem add_comm {p q : Fraction ℤ} : p + q ≃ q + p := by
  revert p; intro (pn//pd); let p := pn//pd
  revert q; intro (qn//qd); let q := qn//qd
  show p + q ≃ q + p
  calc
    _ = p + q                          := rfl
    _ = pn//pd + qn//qd                := rfl
    _ = (pn * qd + pd * qn)//(pd * qd) := rfl
    _ ≃ (qd * pn + pd * qn)//(pd * qd) := by srw [Integer.mul_comm]
    _ ≃ (qd * pn + qn * pd)//(pd * qd) := by srw [Integer.mul_comm]
    _ ≃ (qn * pd + qd * pn)//(pd * qd) := by srw [Integer.add_comm]
    _ ≃ (qn * pd + qd * pn)//(qd * pd) := by srw [Integer.mul_comm]
    _ = qn//qd + pn//pd                := rfl
    _ = q + p                          := rfl

/--
Replacing the left operand in a sum of fractions with an equivalent value gives
an equivalent result.

**Property intuition**: This must be true for addition on fractions to be a
valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
@[gcongr]
theorem add_substL {p₁ p₂ q : Fraction ℤ} : p₁ ≃ p₂ → p₁ + q ≃ p₂ + q := by
  revert p₁; intro (n₁//m₁); let p₁ := n₁//m₁
  revert p₂; intro (n₂//m₂); let p₂ := n₂//m₂
  revert q; intro (k//j); let q := k//j
  intro (_ : p₁ ≃ p₂)
  show p₁ + q ≃ p₂ + q

  have : n₁//m₁ ≃ n₂//m₂ := ‹p₁ ≃ p₂›
  have : n₁ * m₂ ≃ n₂ * m₁ := ‹n₁//m₁ ≃ n₂//m₂›
  have : (n₁ * j + m₁ * k) * (m₂ * j) ≃ (n₂ * j + m₂ * k) * (m₁ * j) := calc
    _ = (n₁ * j + m₁ * k) * (m₂ * j)        := rfl
    _ ≃ ((n₁ * j + m₁ * k) * m₂) * j        := Rel.symm AA.assoc
    _ ≃ ((n₁ * j) * m₂ + (m₁ * k) * m₂) * j := by srw [Integer.mul_distribR]
    _ ≃ ((j * n₁) * m₂ + (m₁ * k) * m₂) * j := by srw [AA.comm]
    _ ≃ (j * (n₁ * m₂) + (m₁ * k) * m₂) * j := by srw [AA.assoc]
    _ ≃ (j * (n₂ * m₁) + (m₁ * k) * m₂) * j := by srw [‹n₁ * m₂ ≃ n₂ * m₁›]
    _ ≃ ((j * n₂) * m₁ + (m₁ * k) * m₂) * j := by srw [←AA.assoc]
    _ ≃ ((j * n₂) * m₁ + m₁ * (k * m₂)) * j := by srw [AA.assoc]
    _ ≃ ((j * n₂) * m₁ + (k * m₂) * m₁) * j := by srw [AA.comm]
    _ ≃ ((j * n₂ + k * m₂) * m₁) * j        := by srw [←Integer.mul_distribR]
    _ ≃ (j * n₂ + k * m₂) * (m₁ * j)        := AA.assoc
    _ ≃ (n₂ * j + k * m₂) * (m₁ * j)        := by srw [AA.comm]
    _ ≃ (n₂ * j + m₂ * k) * (m₁ * j)        := by srw [AA.comm]
  calc
    _ = p₁ + q                := rfl
    _ = n₁//m₁ + k//j         := rfl
    _ = (n₁*j + m₁*k)//(m₁*j) := rfl
    _ ≃ (n₂*j + m₂*k)//(m₂*j) := ‹(n₁*j + m₁*k)*(m₂*j) ≃ (n₂*j + m₂*k)*(m₁*j)›
    _ = n₂//m₂ + k//j         := rfl
    _ = p₂ + q                := rfl

/--
Replacing the right operand in a sum of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for addition on fractions to be a
valid function.

**Proof intuition**: Flip the sum around using commutativity, perform left
substitution, then flip it back.
-/
@[gcongr]
theorem add_substR {p q₁ q₂ : Fraction ℤ} : q₁ ≃ q₂ → p + q₁ ≃ p + q₂ := by
  intro (_ : q₁ ≃ q₂)
  show p + q₁ ≃ p + q₂
  calc
    _ = p + q₁ := rfl
    _ ≃ q₁ + p := add_comm
    _ ≃ q₂ + p := by srw [‹q₁ ≃ q₂›]
    _ ≃ p + q₂ := add_comm

/--
Fraction addition is associative.

**Property intuition**: Fractions are scaled integers, so we expect
associativity to carry over.

**Proof intuition**: Expand definitions until each side of the equivalence is a
single fraction. The denominators are clearly equivalent by associativity of
integer multiplication. The numerators are equivalent via distributivity, and
associativity of addition, over integers.
-/
theorem add_assoc {p q r : Fraction ℤ} : (p + q) + r ≃ p + (q + r) := by
  revert p; intro (n//m); let p := n//m
  revert q; intro (k//j); let q := k//j
  revert r; intro (u//t); let r := u//t
  show (p + q) + r ≃ p + (q + r)

  have int_distribL {a b c : ℤ} : a*(b + c) ≃ a*b + a*c := Integer.mul_distribL
  have int_distribR {a b c : ℤ} : (b + c)*a ≃ b*a + c*a := Integer.mul_distribR
  calc
    _ = (p + q) + r                              := rfl
    _ = (n//m + k//j) + u//t                     := rfl
    _ = (n*j + m*k)//(m*j) + u//t                := rfl
    _ = ((n*j+m*k)*t + (m*j)*u)//((m*j)*t)       := rfl
    _ ≃ (((n*j)*t+(m*k)*t) + (m*j)*u)//((m*j)*t) := by srw [int_distribR]
    _ ≃ ((n*(j*t)+(m*k)*t) + (m*j)*u)//((m*j)*t) := by srw [Integer.mul_assoc]
    _ ≃ ((n*(j*t)+m*(k*t)) + (m*j)*u)//((m*j)*t) := by srw [Integer.mul_assoc]
    _ ≃ ((n*(j*t)+m*(k*t)) + m*(j*u))//((m*j)*t) := by srw [Integer.mul_assoc]
    _ ≃ (n*(j*t) + (m*(k*t)+m*(j*u)))//((m*j)*t) := by srw [Integer.add_assoc]
    _ ≃ (n*(j*t) + m*(k*t+j*u))//((m*j)*t)       := by srw [←int_distribL]
    _ ≃ (n*(j*t) + m*(k*t+j*u))//(m*(j*t))       := by srw [Integer.mul_assoc]
    _ = n//m + (k*t + j*u)//(j*t)                := rfl
    _ = n//m + (k//j + u//t)                     := rfl
    _ = p + (q + r)                              := rfl

/--
Zero is a left identity element for fraction addition.

**Property intuition**: Fractions are scaled integers, so we expect
identity elements to carry over.

**Proof intuition**: Expand definitions, add, and simplify.
-/
theorem add_identL {p : Fraction ℤ} : 0 + p ≃ p := by
  revert p; intro (pn//pd); let p := pn//pd
  show 0 + p ≃ p
  calc
    _ = (0:ℤ)//1 + pn//pd           := rfl
    _ = (0 * pd + 1 * pn)//(1 * pd) := rfl
    _ ≃ (0 + 1 * pn)//(1 * pd)      := by srw [Integer.mul_absorbL]
    _ ≃ (1 * pn)//(1 * pd)          := by srw [Integer.add_identL]
    _ ≃ pn//(1 * pd)                := by srw [Integer.mul_identL]
    _ ≃ pn//pd                      := by srw [Integer.mul_identL]
    _ = p                           := rfl

/--
Zero is a right identity element for fraction addition.

**Property intuition**: Fractions are scaled integers, so we expect
identity elements to carry over.

**Proof intuition**: Combine commutativity with the left identity proof.
-/
theorem add_identR {p : Fraction ℤ} : p + 0 ≃ p :=
  eqv_trans add_comm add_identL

instance addition_props : Addition.Props (Fraction ℤ) := {
  add_substL := add_substL
  add_substR := add_substR
  add_compat_from_integer := add_compat_from_integer
  add_comm := add_comm
  add_assoc := add_assoc
  add_identL := add_identL
  add_identR := add_identR
}

instance addition : Addition (Fraction ℤ) := {
  toOps := addition_ops
  toProps := addition_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
