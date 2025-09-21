import Lean4Axiomatic.Rational.Core
import Lean4Axiomatic.Rational.Impl.Fraction.Naive

namespace Lean4Axiomatic.Rational.Impl

open Logic (AP)
open Relation.Equivalence (EqvOp)
open Signed (Negative Positive Positivity)

/-!
## (True) Fractions

With the knowledge gained from the attempt at naive fractions, we can now make
formal fractions that have the right constraints to be useful as rational
numbers.
-/

/--
A formal fraction of signed values, where the denominator must be positive.

As explored in `Fraction.Naive`, we must at least constrain the denominator to
be nonzero if we want to have a useful definition of fractions. We go a bit
further than that here, and require a positive denominator, because it
simplifies the definition of positive and negative for fractions: only the sign
of the numerator matters.

The `denominator_positive` field is defined with square brackets so that it
becomes an instance parameter in `Fraction`'s constructor, allowing Lean to
automatically fill it in. Otherwise it would frequently require tedious
bookkeeping to manage.

One way to think about values of this type is that they represent a "frozen" or
"unevaluated" division operation between two numbers. If we represent a value
of this type as the expression `n//d`, where `n` is the numerator and `d` is
the denominator, then informally the division concept says `(n//d) * d ≃ n`.

Another viewpoint, also described in the section on naive fractions, is that a
fraction is a numeric value (the numerator) which is at a certain "size" or
"scale" given by the denominator. Using the simple case of integer fractions, a
scale of `1` corresponds with ordinary integers; a scale of `2` means that a
numerator of `2` is the same size as the ordinary integer `1`; and in general
we have `n//n ≃ 1`. Integers at the same scale can be added directly
(`a//n + b//n ≃ (a + b)//n`), and this is what motivates the definition of
addition for fractions.
-/
structure Fraction
    (α : Type) [EqvOp α] [OfNat α 0] [Positivity.Ops α] : Type
    where
  numerator : α
  denominator : α
  [denominator_positive : AP (Positive denominator)]

infix:90 "//" => Fraction.mk

namespace Fraction

/--
The naive representation of this fraction.

This simply drops the positive requirement for the denominator. Mainly good for
reusing naive fraction definitions that still work for true fractions.
-/
def naive
    {α : Type} [EqvOp α] [OfNat α 0] [Positivity.Ops α]
    : Fraction α → Naive.Fraction α
| a//b => Naive.Fraction.mk a b

/--
Lift a naive fraction to a true fraction, if its denominator is positive.
-/
def from_naive
    {α : Type} [EqvOp α] [OfNat α 0] [Positivity.Ops α] (p : Naive.Fraction α)
    : Positive p.denominator → Fraction α
    := by
  revert p; intro (Naive.Fraction.mk pn pd) (_ : Positive pd)
  have : AP (Positive pd) := AP.mk ‹Positive pd›
  exact pn//pd

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/--
Equivalence relation on formal fractions of integers.

See `Naive.eqv` for more explanation.
-/
def eqv (p q : Fraction ℤ) : Prop := Naive.eqv p.naive q.naive

instance equivalence_ops : Equivalence.Ops (Fraction ℤ) := {
  eqv := eqv
}

/-- Fraction equivalence is reflexive. -/
theorem eqv_refl {p : Fraction ℤ} : p ≃ p := Naive.eqv_refl (p := p.naive)

/-- Fraction equivalence is symmetric. -/
theorem eqv_symm {p q : Fraction ℤ} : p ≃ q → q ≃ p :=
  Naive.eqv_symm (p := p.naive) (q := q.naive)

/-- Fraction equivalence is transitive. -/
theorem eqv_trans {p q r : Fraction ℤ} : p ≃ q → q ≃ r → p ≃ r :=
  let qd := q.denominator
  have : Positive qd := q.denominator_positive.ev
  have : Positive qd ∨ Negative qd := Or.inl this
  have : Integer.Nonzero qd := Integer.nonzero_iff_pos_or_neg.mpr this
  have : qd ≄ 0 := Integer.nonzero_iff_neqv_zero.mp this
  Naive.eqv_trans_nonzero_denom
    (p := p.naive) (q := q.naive) (r := r.naive) ‹qd ≄ 0›

instance equivalence_props : Equivalence.Props (Fraction ℤ) := {
  eqv_refl := eqv_refl
  eqv_symm := eqv_symm
  eqv_trans := eqv_trans
}

instance equivalence : Equivalence (Fraction ℤ) := {}

/--
Replacing the numerator of a fraction with an equivalent value gives an
equivalent result.

**Property intuition**: This must be true for fractions to be a useful data
structure.

**Proof intuition**: Expand the definition of equivalence; use substitution of
integer multiplication.
-/
@[gcongr]
theorem substN {a₁ a₂ b : ℤ} [AP (Positive b)] : a₁ ≃ a₂ → a₁//b ≃ a₂//b := by
  intro (_ : a₁ ≃ a₂)
  show a₁//b ≃ a₂//b
  show a₁ * b ≃ a₂ * b
  srw [‹a₁ ≃ a₂›]

/--
Replacing the denominator of a fraction with an equivalent value gives an
equivalent result.

**Property intuition**: This must be true for fractions to be a useful data
structure.

**Proof intuition**: Expand the definition of equivalence; use substitution of
integer multiplication.
-/
@[gcongr]
theorem substD
    {a b₁ b₂ : ℤ} [pb₁ : AP (Positive b₁)] [pb₂ : AP (Positive b₂)]
    : b₁ ≃ b₂ → a//b₁ ≃ a//b₂
    := by
  intro (_ : b₁ ≃ b₂)
  show a//b₁ ≃ a//b₂
  show a * b₂ ≃ a * b₁
  srw [←‹b₁ ≃ b₂›]

/--
Every integer can be represented as a fraction.

**Intuition**: Dividing by `1` leaves the input unchanged. Or, a denominator of
`1` means that every unit of the numerator is the same "size" as the integer
`1`.
-/
def from_integer : ℤ → Fraction ℤ := (·//1)

instance conversion_ops : Conversion.Ops (ℤ := ℤ) (Fraction ℤ) := {
  from_integer := from_integer
}

/--
Equivalent integers are converted to equivalent integer fractions.

**Property intuition**: This must be true if we want integer fractions to be a
superset of the integers.

**Proof intuition**: The denominators are identical, so the result follows from
the equivalence of the numerators.
-/
@[gcongr]
theorem from_integer_subst
    {a₁ a₂ : ℤ} : a₁ ≃ a₂ → from_integer a₁ ≃ from_integer a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show from_integer a₁ ≃ from_integer a₂
  calc
    _ = from_integer a₁ := rfl
    _ = a₁//1           := rfl
    _ ≃ a₂//1           := by srw [‹a₁ ≃ a₂›]
    _ = from_integer a₂ := rfl

/--
Equivalent converted fractions came from the same integer.

**Property intuition**: Every integer must have a unique representation as an
integer fraction.

**Proof intuition**: Expand the hypothesis into an equivalence on integers.
Cancel the common factor to obtain the result.
-/
theorem from_integer_inject
    {a₁ a₂ : ℤ} : from_integer a₁ ≃ from_integer a₂ → a₁ ≃ a₂
    := by
  intro (_ : from_integer a₁ ≃ from_integer a₂)
  show a₁ ≃ a₂
  have : a₁//1 ≃ a₂//1 := ‹from_integer a₁ ≃ from_integer a₂›
  have : a₁ * 1 ≃ a₂ * 1 := this
  have : a₁ ≃ a₂ := AA.cancelRC (C := (· ≄ 0)) Integer.one_neqv_zero this
  exact this

instance conversion_props : Conversion.Props (Fraction ℤ) := {
  from_integer_subst := from_integer_subst
  from_integer_inject := from_integer_inject
}

instance conversion : Conversion (ℤ := ℤ) (Fraction ℤ) := {
  toOps := conversion_ops
  toProps := conversion_props
}

instance core : Core (ℤ := ℤ) (Fraction ℤ) := {
  toEquivalence := equivalence
  toConversion := conversion
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
An integer fraction that's not equivalent to zero has a nonzero numerator.

This lemma is helpful for saving a few steps in proofs.

**Property and proof intuition**: Follows directly from integer fractions being
zero iff their numerators are.
-/
theorem nonzero_numerator
    (p : Fraction ℤ) [AP (p ≄ 0)] : Integer.Nonzero p.numerator
    := by
  revert p; intro (a//b) (_ : AP (a//b ≄ 0))
  have : a ≃ 0 → a//b ≃ 0 := (eqv_zero_iff_numerator_eqv_zero (p := a//b)).mpr
  have : a ≄ 0 := mt this ‹AP (a//b ≄ 0)›.ev
  have : Integer.Nonzero a := Integer.nonzero_iff_neqv_zero.mpr this
  exact this

/--
Fractions are equivalent to one exactly when their numerators and denominators
are equivalent.

**Property intuition**: The denominator of a fraction denotes what the quantity
of the numerator must be for the fraction to be equivalent to one, and that's
exactly what this property expresses.

**Proof intuition**: In both directions, expand equivalence between fractions
into equivalence between integers. The goals follow easily from integer facts.
-/
theorem eqv_one_iff_numer_eqv_denom
    {p : Fraction ℤ} : p ≃ 1 ↔ p.numerator ≃ p.denominator
    := by
  revert p; intro (pn//pd); let p := pn//pd
  show p ≃ 1 ↔ p.numerator ≃ p.denominator
  calc
    _ ↔ p ≃ 1                       := Iff.rfl
    _ ↔ pn//pd ≃ 1//1               := Iff.rfl
    _ ↔ pn * 1 ≃ 1 * pd             := Iff.rfl
    _ ↔ pn ≃ 1 * pd                 := by srw [Integer.mul_identR]
    _ ↔ pn ≃ pd                     := by srw [Integer.mul_identL]
    _ ↔ p.numerator ≃ p.denominator := Iff.rfl

end Lean4Axiomatic.Rational.Impl.Fraction
