import Lean4Axiomatic.Rational.Impl.Fraction.Addition

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Integer (Nonzero)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer ℕ ℤ]

/-! ## Fraction multiplication -/

/-- Multiplication of fractions. -/
def mul : Fraction ℤ → Fraction ℤ → Fraction ℤ
| p//q, r//s => (p * r)//(q * s)

instance mulOp : Mul (Fraction ℤ) := {
  mul := mul
}

/--
Multiplication of fractions is commutative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Expand all definitions in the goal until an equivalence
involving only integers is reached. Show this equivalence using algebra.
-/
theorem mul_comm {p q : Fraction ℤ} : p * q ≃ q * p := by
  revert p; intro (pn//pd); revert q; intro (qn//qd)
  show pn//pd * qn//qd ≃ qn//qd * pn//pd
  show (pn * qn)//(pd * qd) ≃ (qn * pn)//(qd * pd)
  show (pn * qn) * (qd * pd) ≃ (qn * pn) * (pd * qd)
  calc
    (pn * qn) * (qd * pd) ≃ _ := AA.substL AA.comm
    (qn * pn) * (qd * pd) ≃ _ := AA.substR AA.comm
    (qn * pn) * (pd * qd) ≃ _ := Rel.refl

/--
Replacing the left operand in a product of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for multiplication on fractions to be
a valid function.

**Proof intuition**: Expand all definitions in the hypotheses and goal until
equivalences involving only integers are reached. Show the goal equivalence
using algebra and the equivalence from the `p₁ ≃ p₂` hypothesis.
-/
theorem mul_substL {p₁ p₂ q : Fraction ℤ} : p₁ ≃ p₂ → p₁ * q ≃ p₂ * q := by
  revert p₁; intro (p₁n//p₁d); revert p₂; intro (p₂n//p₂d)
  revert q; intro (qn//qd)
  intro (_ : p₁n//p₁d ≃ p₂n//p₂d)
  show p₁n//p₁d * qn//qd ≃ p₂n//p₂d * qn//qd
  show (p₁n * qn)//(p₁d * qd) ≃ (p₂n * qn)//(p₂d * qd)
  show (p₁n * qn) * (p₂d * qd) ≃ (p₂n * qn) * (p₁d * qd)
  have : p₁n * p₂d ≃ p₂n * p₁d := ‹p₁n//p₁d ≃ p₂n//p₂d›
  calc
    (p₁n * qn) * (p₂d * qd) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (p₁n * p₂d) * (qn * qd) ≃ _ := AA.substL ‹p₁n * p₂d ≃ p₂n * p₁d›
    (p₂n * p₁d) * (qn * qd) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (p₂n * qn) * (p₁d * qd) ≃ _ := Rel.refl

/--
Replacing the right operand in a product of fractions with an equivalent value
gives an equivalent result.

**Property intuition**: This must be true for multiplication on fractions to be
a valid function.

**Proof intuition**: Flip the product around using commutativity, perform left
substitution, then flip it back.
-/
theorem mul_substR {p q₁ q₂ : Fraction ℤ} : q₁ ≃ q₂ → p * q₁ ≃ p * q₂ := by
  intro (_ : q₁ ≃ q₂)
  show p * q₁ ≃ p * q₂
  calc
    p * q₁ ≃ _ := mul_comm
    q₁ * p ≃ _ := mul_substL ‹q₁ ≃ q₂›
    q₂ * p ≃ _ := mul_comm
    p * q₂ ≃ _ := eqv_refl

/--
Fraction multiplication is associative.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Evaluate all multiplications until a single fraction is
obtained. Associativity on its numerator and denominator gives the result.
-/
theorem mul_assoc {p q r : Fraction ℤ} : (p * q) * r ≃ p * (q * r) := by
  revert p; intro (pn//pd); revert q; intro (qn//qd); revert r; intro (rn//rd)
  show (pn//pd * qn//qd) * rn//rd ≃ pn//pd * (qn//qd * rn//rd)
  calc
    (pn//pd * qn//qd) * rn//rd         ≃ _ := eqv_refl
    (pn * qn)//(pd * qd) * rn//rd      ≃ _ := eqv_refl
    ((pn * qn) * rn)//((pd * qd) * rd) ≃ _ := substL AA.assoc
    (pn * (qn * rn))//((pd * qd) * rd) ≃ _ := substR AA.assoc
    (pn * (qn * rn))//(pd * (qd * rd)) ≃ _ := eqv_refl
    pn//pd * (qn * rn)//(qd * rd)      ≃ _ := eqv_refl
    pn//pd * (qn//qd * rn//rd)         ≃ _ := eqv_refl

/--
One is the left multiplicative identity for fractions.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Evaluate the multiplication to obtain a single fraction.
Use the integer multiplicative identity on its numerator and denominator.
-/
theorem mul_identL {p : Fraction ℤ} : 1 * p ≃ p := by
  revert p; intro (pn//pd)
  show 1 * pn//pd ≃ pn//pd
  calc
    1 * pn//pd         ≃ _ := eqv_refl
    1//1 * pn//pd      ≃ _ := eqv_refl
    (1 * pn)//(1 * pd) ≃ _ := substL AA.identL
    pn//(1 * pd)       ≃ _ := substR AA.identL
    pn//pd             ≃ _ := eqv_refl

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
    {a b c : ℤ} [Nonzero a] [Nonzero c] : (a * b)//(a * c) ≃ b//c
    := calc
  (a * b)//(a * c)
    ≃ _ := eqv_refl
  a//a * b//c
    ≃ _ := mul_substL (eqv_one_iff_numerator_eqv_denominator.mpr Rel.refl)
  1 * b//c
    ≃ _ := mul_identL
  b//c
    ≃ _ := eqv_refl

/--
A common factor on the right of the numerator and denominator can be removed.

**Property and proof intuition**: This follows from left-cancellation and
commutativity.
-/
theorem cancelR
    {a b c : ℤ} [Nonzero a] [Nonzero c] : (b * a)//(c * a) ≃ b//c
    := calc
  (b * a)//(c * a) ≃ _ := substL AA.comm
  (a * b)//(c * a) ≃ _ := substR AA.comm
  (a * b)//(a * c) ≃ _ := cancelL
  b//c             ≃ _ := eqv_refl

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
    {a b d : ℤ} [Nonzero d] : a//d + b//d ≃ (a + b)//d
    := calc
  a//d + b//d
    ≃ _ := eqv_refl
  (a * d + d * b)//(d * d)
    ≃ _ := substL (AA.substR AA.comm)
  (a * d + b * d)//(d * d)
    ≃ _ := substL (Rel.symm AA.distribR)
  ((a + b) * d)//(d * d)
    ≃ _ := cancelR
  (a + b)//d
    ≃ _ := eqv_refl

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
  revert p; intro (pn//pd); revert q; intro (qn//qd); revert r; intro (rn//rd)
  show pn//pd * (qn//qd + rn//rd) ≃ pn//pd * qn//qd + pn//pd * rn//rd
  have : Nonzero (pd * (rd * qd)) := Integer.mul_preserves_nonzero_inst
  calc
    pn//pd * (qn//qd + rn//rd)
      ≃ _ := eqv_refl
    pn//pd * (qn * rd + qd * rn)//(qd * rd)
      ≃ _ := eqv_refl
    (pn * (qn * rd + qd * rn))//(pd * (qd * rd))
      ≃ _ := substL AA.distribL
    (pn * (qn * rd) + pn * (qd * rn))//(pd * (qd * rd))
      ≃ _ := eqv_symm add_eqv_denominators
    (pn * (qn * rd))//(pd * (qd * rd)) + (pn * (qd * rn))//(pd * (qd * rd))
      ≃ _ := add_substL (substL (Rel.symm AA.assoc))
    ((pn * qn) * rd)//(pd * (qd * rd)) + (pn * (qd * rn))//(pd * (qd * rd))
      ≃ _ := add_substL (substR (Rel.symm AA.assoc))
    ((pn * qn) * rd)//((pd * qd) * rd) + (pn * (qd * rn))//(pd * (qd * rd))
      ≃ _ := add_substL cancelR
    (pn * qn)//(pd * qd) + (pn * (qd * rn))//(pd * (qd * rd))
      ≃ _ := add_substR (substL (AA.substR AA.comm))
    (pn * qn)//(pd * qd) + (pn * (rn * qd))//(pd * (qd * rd))
      ≃ _ :=
        add_substR
          (substR (nz₂ := ‹Nonzero (pd * (rd * qd))›) (AA.substR AA.comm))
    (pn * qn)//(pd * qd) + (pn * (rn * qd))//(pd * (rd * qd))
      ≃ _ := add_substR (substL (Rel.symm AA.assoc))
    (pn * qn)//(pd * qd) + ((pn * rn) * qd)//(pd * (rd * qd))
      ≃ _ := add_substR (substR (Rel.symm AA.assoc))
    (pn * qn)//(pd * qd) + ((pn * rn) * qd)//((pd * rd) * qd)
      ≃ _ := add_substR cancelR
    (pn * qn)//(pd * qd) + (pn * rn)//(pd * rd)
      ≃ _ := eqv_refl
    pn//pd * qn//qd + (pn * rn)//(pd * rd)
      ≃ _ := eqv_refl
    pn//pd * qn//qd + pn//pd * rn//rd
      ≃ _ := eqv_refl

/--
Fraction multiplication (on the right) distributes over fraction addition.

**Property intuition**: We'd expect this to be true due to the viewpoint that
fractions are scaled integers.

**Proof intuition**: Follows from left-distributivity and commutativity of
addition and multiplication.
-/
theorem mul_distribR {p q r : Fraction ℤ} : (q + r) * p ≃ q * p + r * p := calc
  (q + r) * p   ≃ _ := mul_comm
  p * (q + r)   ≃ _ := mul_distribL
  p * q + p * r ≃ _ := add_substL mul_comm
  q * p + p * r ≃ _ := add_substR mul_comm
  q * p + r * p ≃ _ := eqv_refl

end Lean4Axiomatic.Rational.Impl.Fraction
