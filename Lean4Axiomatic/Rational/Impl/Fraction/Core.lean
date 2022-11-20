import Lean4Axiomatic.Rational.Impl.Fraction.Naive

namespace Lean4Axiomatic.Rational.Impl

open Integer (Nonzero)

/-!
## (True) Fractions

With the knowledge gained from the attempt at naive fractions, we can now make
formal fractions that have the right constraints to be useful as rational
numbers.
-/

/--
A formal fraction of integer values, where the denominator must be nonzero.

Currently the `Nonzero` predicate is only defined on integers, so we cannot
generalize this fraction to arbitrary types as we did with naive fractions. The
`denominator_nonzero` field is defined with the `instance` attribute so that it
can be automatically filled in by Lean. Otherwise it would frequently require
tedious bookkeeping to manage.

One way to think about values of this type is that they represent a "frozen" or
"unevaluated" division operation between two integers. If we represent a value
of this type as the expression `n//d`, where `n` is the numerator and `d` is
the denominator, then informally the division concept says `(n//d) * d ≃ n`.

Another viewpoint, also described in the section on naive fractions, is that a
fraction is an integer value (the numerator) which is at a certain "size" or
"scale" given by the denominator. A scale of `1` corresponds with ordinary
integers; a scale of `2` means that a numerator of `2` is the same size as the
ordinary integer `1`; and in general we have `n//n ≃ 1`. Integers at the same
scale can be added directly (`a//n + b//n ≃ (a + b)//n`), and this is what
motivates the definition of addition for fractions.
-/
structure Fraction {ℕ : Type} [Natural ℕ] (ℤ : Type) [Integer ℕ ℤ] : Type :=
  numerator : ℤ
  denominator : ℤ
  [denominator_nonzero : Nonzero denominator]

namespace Fraction

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer ℕ ℤ]

infix:90 "//" => Fraction.mk

/--
The naive representation of this fraction.

This simply drops the nonzero requirement for the denominator. Mainly good for
reusing naive fraction definitions that still work for true fractions.
-/
def naive : Fraction ℤ → Naive.Fraction ℤ
| a//b => Naive.Fraction.mk a b

/-- Lift a naive fraction to a true fraction, if its denominator is nonzero. -/
def from_naive
    (p : Naive.Fraction ℤ) : Nonzero p.denominator → Fraction ℤ
    := by
  revert p; intro (Naive.Fraction.mk pn pd) (_ : Nonzero pd)
  exact pn//pd

/--
Equivalence relation on formal fractions of integers.

See `Naive.eqv` for more explanation.
-/
def eqv (p q : Fraction ℤ) : Prop := Naive.eqv p.naive q.naive

instance tildeDash : Operators.TildeDash (Fraction ℤ) := {
  tildeDash := eqv
}

/-- Fraction equivalence is reflexive. -/
theorem eqv_refl {p : Fraction ℤ} : p ≃ p := Naive.eqv_refl (p := p.naive)

/-- Fraction equivalence is symmetric. -/
theorem eqv_symm {p q : Fraction ℤ} : p ≃ q → q ≃ p :=
  Naive.eqv_symm (p := p.naive) (q := q.naive)

/-- Fraction equivalence is transitive. -/
theorem eqv_trans {p q r : Fraction ℤ} : p ≃ q → q ≃ r → p ≃ r :=
  have : q.denominator ≄ 0 :=
    Integer.nonzero_iff_neqv_zero.mp q.denominator_nonzero
  Naive.eqv_trans_nonzero_denom
    (p := p.naive) (q := q.naive) (r := r.naive) ‹q.denominator ≄ 0›

instance eqvOp : Relation.Equivalence.EqvOp (Fraction ℤ) := {
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans
}

/--
Replacing the numerator of a fraction with an equivalent value gives an
equivalent result.

**Property intuition**: This must be true for fractions to be a useful data
structure.

**Proof intuition**: Expand the definition of equivalence; use substitution of
integer multiplication.
-/
theorem substL {a₁ a₂ b : ℤ} [Nonzero b] : a₁ ≃ a₂ → a₁//b ≃ a₂//b := by
  intro (_ : a₁ ≃ a₂)
  show a₁//b ≃ a₂//b
  show a₁ * b ≃ a₂ * b
  exact AA.substL ‹a₁ ≃ a₂›

/--
Replacing the denominator of a fraction with an equivalent value gives an
equivalent result.

**Property intuition**: This must be true for fractions to be a useful data
structure.

**Proof intuition**: Expand the definition of equivalence; use substitution of
integer multiplication.
-/
theorem substR
    {a b₁ b₂ : ℤ} [Nonzero b₁] [Nonzero b₂] : b₁ ≃ b₂ → a//b₁ ≃ a//b₂
    := by
  intro (_ : b₁ ≃ b₂)
  show a//b₁ ≃ a//b₂
  show a * b₂ ≃ a * b₁
  exact AA.substR (Rel.symm ‹b₁ ≃ b₂›)

/--
Every integer can be represented as a fraction.

**Intuition**: Dividing by `1` leaves the input unchanged. Or, a denominator of
`1` means that every unit of the numerator is the same "size" as the integer
`1`.
-/
instance from_integer : Coe ℤ (Fraction ℤ) := {
  coe := (·//1)
}

/-- Natural number literals can be converted into fractions. -/
instance literal {n : Nat} : OfNat (Fraction ℤ) n := {
  ofNat := Coe.coe (OfNat.ofNat n : ℤ)
}

/--
Fractions are equivalent to zero exactly when their numerators are.

**Property intuition**: The numerator of a fraction is the integer value that
is "scaled down" by the denominator. So the fraction should represent zero only
when its numerator is zero, and vice versa.

**Proof intuition**: In both directions, expand equivalence between fractions
into equivalence between integers. The goals follow easily from integer facts.
-/
theorem eqv_zero_iff_numerator_eqv_zero
    {p : Fraction ℤ} : p ≃ 0 ↔ p.numerator ≃ 0
    := by
  revert p; intro (pn//pd)
  apply Iff.intro
  case mp =>
    intro (_ : pn//pd ≃ 0)
    show pn ≃ 0
    have : pn//pd ≃ 0//1 := ‹pn//pd ≃ 0›
    have : pn * 1 ≃ 0 * pd := ‹pn//pd ≃ 0//1›
    calc
      pn     ≃ _ := Rel.symm AA.identR
      pn * 1 ≃ _ := ‹pn * 1 ≃ 0 * pd›
      0 * pd ≃ _ := AA.absorbL
      0      ≃ _ := Rel.refl
  case mpr =>
    intro (_ : pn ≃ 0)
    show pn//pd ≃ 0
    show pn//pd ≃ 0//1
    show pn * 1 ≃ 0 * pd
    calc
      pn * 1 ≃ _ := AA.identR
      pn     ≃ _ := ‹pn ≃ 0›
      0      ≃ _ := Rel.symm AA.absorbL
      0 * pd ≃ _ := Rel.refl

/--
Fractions are equivalent to one exactly when their numerators and denominators
are equivalent.

**Property intuition**: The denominator of a fraction denotes what the quantity
of the numerator must be for the fraction to be equivalent to one, and that's
exactly what this property expresses.

**Proof intuition**: In both directions, expand equivalence between fractions
into equivalence between integers. The goals follow easily from integer facts.
-/
theorem eqv_one_iff_numerator_eqv_denominator
    {p : Fraction ℤ} : p ≃ 1 ↔ p.numerator ≃ p.denominator
    := by
  revert p; intro (pn//pd)
  apply Iff.intro
  case mp =>
    intro (_ : pn//pd ≃ 1)
    show pn ≃ pd
    have : pn//pd ≃ 1//1 := ‹pn//pd ≃ 1//1›
    have : pn * 1 ≃ 1 * pd := ‹pn//pd ≃ 1//1›
    calc
      pn     ≃ _ := Rel.symm AA.identR
      pn * 1 ≃ _ := ‹pn * 1 ≃ 1 * pd›
      1 * pd ≃ _ := AA.identL
      pd     ≃ _ := Rel.refl
  case mpr =>
    intro (_ : pn ≃ pd)
    show pn//pd ≃ 1
    show pn//pd ≃ 1//1
    show pn * 1 ≃ 1 * pd
    calc
      pn * 1 ≃ _ := AA.substL ‹pn ≃ pd›
      pd * 1 ≃ _ := AA.comm
      1 * pd ≃ _ := Rel.refl

end Lean4Axiomatic.Rational.Impl.Fraction
