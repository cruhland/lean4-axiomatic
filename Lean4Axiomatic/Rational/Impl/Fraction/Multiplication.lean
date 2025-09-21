import Lean4Axiomatic.Rational.Impl.Fraction.Addition
import Lean4Axiomatic.Rational.Multiplication

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Logic (AP)
open Signed (Positive)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/-! ## Fraction multiplication -/

/-- Multiplication of fractions. -/
def mul : Fraction ℤ → Fraction ℤ → Fraction ℤ
| p//q, r//s => (p * r)//(q * s)

instance multiplication_ops : Multiplication.Ops (Fraction ℤ) := {
  mul := mul
}

/--
Multiplication of integer fractions is consistent with its equivalent on
integers.

**Property intuition**: This must be true if we want integers to be represented
as integer fractions.

**Proof intuition**: Expand the definition of multiplication and use integer
algebra on the numerator and denominator.
-/
theorem mul_compat_from_integer
    {a b : ℤ} : from_integer (a * b) ≃ from_integer a * from_integer b
    := eqv_symm $ calc
  _ = from_integer a * from_integer b := rfl
  _ = a//1 * b//1                     := rfl
  _ = (a * b)//(1 * 1)                := rfl
  _ ≃ (a * b)//1                      := by srw [Integer.mul_identL]
  _ = from_integer (a * b)            := rfl

/--
Multiplication of integer fractions is commutative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Expand the definition of multiplication and use integer
algebra on the numerator and denominator.
-/
theorem mul_comm {p q : Fraction ℤ} : p * q ≃ q * p := by
  revert p; intro (pn//pd); let p := pn//pd
  revert q; intro (qn//qd); let q := qn//qd
  show p * q ≃ q * p
  calc
    _ = p * q                := rfl
    _ = pn//pd * qn//qd      := rfl
    _ = (pn * qn)//(pd * qd) := rfl
    _ ≃ (qn * pn)//(qd * pd) := by srw [Integer.mul_comm, Integer.mul_comm]
    _ = qn//qd * pn//pd      := rfl
    _ = q * p                := rfl

/--
Replacing the left operand in a product of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for multiplication on fractions to be
a valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
@[gcongr]
theorem mul_substL {p₁ p₂ q : Fraction ℤ} : p₁ ≃ p₂ → p₁ * q ≃ p₂ * q := by
  revert p₁; intro (n₁//m₁); let p₁ := n₁//m₁
  revert p₂; intro (n₂//m₂); let p₂ := n₂//m₂
  revert q; intro (k//j); let q := k//j
  intro (_ : p₁ ≃ p₂)
  show p₁ * q ≃ p₂ * q

  have : n₁ * m₂ ≃ n₂ * m₁ := ‹n₁//m₁ ≃ n₂//m₂›
  have : (n₁ * k) * (m₂ * j) ≃ (n₂ * k) * (m₁ * j) := calc
    _ = (n₁ * k) * (m₂ * j) := rfl
    _ ≃ (n₁ * m₂) * (k * j) := AA.expr_xxfxxff_lr_swap_rl
    _ ≃ (n₂ * m₁) * (k * j) := by srw [‹n₁ * m₂ ≃ n₂ * m₁›]
    _ ≃ (n₂ * k) * (m₁ * j) := AA.expr_xxfxxff_lr_swap_rl
  calc
    _ = p₁ * q             := rfl
    _ = n₁//m₁ * k//j      := rfl
    _ = (n₁ * k)//(m₁ * j) := rfl
    _ ≃ (n₂ * k)//(m₂ * j) := ‹(n₁ * k) * (m₂ * j) ≃ (n₂ * k) * (m₁ * j)›
    _ = n₂//m₂ * k//j      := rfl
    _ = p₂ * q             := rfl

/--
Replacing the right operand in a product of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for multiplication on fractions to be
a valid function.

**Proof intuition**: Flip the product around using commutativity, perform left
substitution, then flip it back.
-/
@[gcongr]
theorem mul_substR {p q₁ q₂ : Fraction ℤ} : q₁ ≃ q₂ → p * q₁ ≃ p * q₂ := by
  intro (_ : q₁ ≃ q₂)
  show p * q₁ ≃ p * q₂
  calc
    _ = p * q₁ := rfl
    _ ≃ q₁ * p := mul_comm
    _ ≃ q₂ * p := by srw [‹q₁ ≃ q₂›]
    _ ≃ p * q₂ := mul_comm

/--
Fraction multiplication is associative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Evaluate all multiplications until a single fraction is
obtained. Associativity on its numerator and denominator gives the result.
-/
theorem mul_assoc {p q r : Fraction ℤ} : (p * q) * r ≃ p * (q * r) := by
  revert p; intro (pn//pd); let p := pn//pd
  revert q; intro (qn//qd); let q := qn//qd
  revert r; intro (rn//rd); let r := rn//rd
  show (p * q) * r ≃ p * (q * r)
  calc
    _ = (p * q) * r                        := rfl
    _ = (pn//pd * qn//qd) * rn//rd         := rfl
    _ = (pn * qn)//(pd * qd) * rn//rd      := rfl
    _ = ((pn * qn) * rn)//((pd * qd) * rd) := rfl
    _ ≃ (pn * (qn * rn))//((pd * qd) * rd) := by srw [Integer.mul_assoc]
    _ ≃ (pn * (qn * rn))//(pd * (qd * rd)) := by srw [Integer.mul_assoc]
    _ = pn//pd * (qn * rn)//(qd * rd)      := rfl
    _ = pn//pd * (qn//qd * rn//rd)         := rfl
    _ = p * (q * r)                        := rfl

/--
One is the left multiplicative identity for fractions.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Evaluate the multiplication to obtain a single fraction.
Use the integer multiplicative identity on its numerator and denominator.
-/
theorem mul_identL {p : Fraction ℤ} : 1 * p ≃ p := by
  revert p; intro (pn//pd); let p := pn//pd
  show 1 * p ≃ p
  calc
    _ = 1 * p              := rfl
    _ = 1 * pn//pd         := rfl
    _ = 1//1 * pn//pd      := rfl
    _ = (1 * pn)//(1 * pd) := rfl
    _ ≃ pn//pd             := by srw [Integer.mul_identL, Integer.mul_identL]
    _ = p                  := rfl

/--
One is the right multiplicative identity for fractions.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Follows from left identity via commutativity.
-/
theorem mul_identR {p : Fraction ℤ} : p * 1 ≃ p :=
  eqv_trans mul_comm mul_identL

/--
A common factor on the left of the numerator and denominator can be removed.

**Property and proof intuition**: A fraction of products, in the numerator and
denominator, is equivalent to a product of fractions of the factors. If the two
factors on the left of the numerator and denominator are the same, then the
corresponding fraction factor is equivalent to one, and doesn't contribute to
the result.
-/
theorem cancelL
    {a b c : ℤ} [AP (Positive a)] [AP (Positive c)] : (a * b)//(a * c) ≃ b//c
    := calc
  _ = (a * b)//(a * c) := rfl
  _ = a//a * b//c      := rfl
  _ ≃ 1 * b//c         := by srw [eqv_one_iff_numer_eqv_denom.mpr Rel.refl]
  _ ≃ b//c             := mul_identL

/--
A common factor on the right of the numerator and denominator can be removed.

**Property and proof intuition**: This follows from left-cancellation and
commutativity.
-/
theorem cancelR
    {a b c : ℤ} [AP (Positive a)] [AP (Positive c)] : (b * a)//(c * a) ≃ b//c
    := calc
  _ = (b * a)//(c * a) := rfl
  _ ≃ (a * b)//(a * c) := by srw [Integer.mul_comm, Integer.mul_comm]
  _ ≃ b//c             := cancelL

/--
Addition of fractions with the same denominator can be accomplished by adding
their numerators.

**Property intuition**: The numerators are at the same "scale" because the
denominators are the same, so they can be added as integers.

**Proof intuition**: Evaluate the addition, then pull out the common factor of
`d` in the numerator using integer distributivity. With a factor of `d` in the
numerator and denominator, the fraction is the result of multiplication by
`d//d`, which is `1`. So the common factor can be removed, achieving the goal.
-/
theorem add_eqv_denominators
    {a b d : ℤ} [AP (Positive d)] : a//d + b//d ≃ (a + b)//d
    := calc
  _ = a//d + b//d              := rfl
  _ = (a * d + d * b)//(d * d) := rfl
  _ ≃ (a * d + b * d)//(d * d) := by srw [AA.comm]
  _ ≃ ((a + b) * d)//(d * d)   := by srw [←Integer.mul_distribR]
  _ ≃ (a + b)//d               := cancelR

/--
Fraction multiplication (on the left) distributes over fraction addition.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Evaluate the addition and multiplication of the left-hand
side to produce a single fraction. Use integer distributivity to make the
numerator a sum. Split the fraction into a sum of fractions with the same
denominator. Cancel common factors and separate each term into a product of the
input fractions.
-/
theorem mul_distribL {p q r : Fraction ℤ} : p * (q + r) ≃ p * q + p * r := by
  revert p; intro (n//m); let p := n//m
  revert q; intro (k//j); let q := k//j
  revert r; intro (u//t); let r := u//t
  show p * (q + r) ≃ p * q + p * r

  /- Shorter aliases for theorems, to fit them in the below `calc` block. -/
  have int_distribL {a b c : ℤ} : a*(b + c) ≃ a*b + a*c := Integer.mul_distribL
  have add_same_denoms
      {a b d : ℤ} [AP (Positive d)] : a//d + b//d ≃ (a + b)//d
      :=
    add_eqv_denominators

  calc
    _ = p * (q + r)                                 := rfl
    _ = n//m * (k//j + u//t)                        := rfl
    _ = n//m * (k*t + j*u)//(j*t)                   := rfl
    _ = (n*(k*t + j*u))//(m*(j*t))                  := rfl
    _ ≃ (n*(k*t) + n*(j*u))//(m*(j*t))              := by srw [int_distribL]
    _ ≃ (n*(k*t))//(m*(j*t)) + (n*(j*u))//(m*(j*t)) := eqv_symm add_same_denoms
    _ ≃ ((n*k)*t)//(m*(j*t)) + (n*(j*u))//(m*(j*t)) := by srw [←AA.assoc]
    _ ≃ ((n*k)*t)//((m*j)*t) + (n*(j*u))//(m*(j*t)) := by srw [←AA.assoc]
    _ ≃ (n*k)//(m*j) + (n*(j*u))//(m*(j*t))         := by srw [cancelR]
    _ ≃ (n*k)//(m*j) + (n*(u*j))//(m*(j*t))         := by srw [AA.comm]
    _ ≃ (n*k)//(m*j) + (n*(u*j))//(m*(t*j))         := by srw [AA.comm]
    _ ≃ (n*k)//(m*j) + ((n*u)*j)//(m*(t*j))         := by srw [←AA.assoc]
    _ ≃ (n*k)//(m*j) + ((n*u)*j)//((m*t)*j)         := by srw [←AA.assoc]
    _ ≃ (n*k)//(m*j) + (n*u)//(m*t)                 := by srw [cancelR]
    _ = n//m * k//j + n//m * u//t                   := rfl
    _ = p * q + p * r                               := rfl

/--
Fraction multiplication (on the right) distributes over fraction addition.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Follows from left-distributivity and commutativity of
addition and multiplication.
-/
theorem mul_distribR {p q r : Fraction ℤ} : (q + r) * p ≃ q * p + r * p := calc
  _ = (q + r) * p   := rfl
  _ ≃ p * (q + r)   := mul_comm
  _ ≃ p * q + p * r := mul_distribL
  _ ≃ q * p + r * p := by srw [mul_comm, mul_comm]

instance multiplication_props : Multiplication.Props (Fraction ℤ) := {
  mul_substL := mul_substL
  mul_substR := mul_substR
  mul_compat_from_integer := mul_compat_from_integer
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  mul_identL := mul_identL
  mul_identR := mul_identR
  mul_distribL := mul_distribL
  mul_distribR := mul_distribR
}

instance multiplication : Multiplication (Fraction ℤ) := {
  toOps := multiplication_ops
  toProps := multiplication_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
