import Lean4Axiomatic.Integer

namespace Lean4Axiomatic.Rational.Impl.Fraction.Naive

open Coe (coe)
open Integer (Nonzero)
open Natural (step)
open Signed (Positive)

/-!
## Naive fractions

What happens if we put two integers into a fraction without the usual
requirement that the denominator is nonzero?
-/

/--
A "naive" formal fraction of values from an arbitrary type `α`.

We don't require the denominator to be nonzero here. Quite a few of the results
for "normal" fractions still apply to these unrestricted ones. But there are
also some important differences, showing why restricting the denominator is
needed.
-/
structure Fraction (α : Type) : Type :=
  numerator : α
  denominator : α

local infix:90 "//" => Naive.Fraction.mk

/--
Create an ordered pair of `α` values from a `Naive.Fraction α`.

Sometimes it can be helpful to have a strict form of equivalence between
naive fractions, one that works component-wise; conversion to ordered pairs
enables this.
-/
def Fraction.to_prod {α : Type} : Naive.Fraction α → α × α
| a//b => (a, b)

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ]

/--
An attempted equivalence relation on naive fractions of integers.

Based on the fundamental notion that fractions represent division, the inverse
of multiplication. Informally, we want the following line of reasoning to hold:
1. `p//q ≃ r//s`
2. `(p//q) * q ≃ (r//s) * q`
3. `p ≃ (r * q)//s`
4. `p * s ≃ ((r * q)//s) * s`
5. `p * s ≃ r * q`

This has the same form as the equivalence relation on traditional fractions,
but it's not actually an equivalence relation because it fails to be transitive
(see proofs below).
-/
def eqv : Naive.Fraction ℤ → Naive.Fraction ℤ → Prop
| p//q, r//s => p * s ≃ r * q

/-- Provide the `· ≃ ·` operator for equivalence of naive fractions. -/
instance tildeDash : Operators.TildeDash (Naive.Fraction ℤ) := {
  tildeDash := eqv
}

/-- Naive fraction equivalence is reflexive. -/
theorem eqv_refl {p : Naive.Fraction ℤ} : p ≃ p := by
  revert p; intro (a//b)
  show a//b ≃ a//b
  show a * b ≃ a * b
  exact Rel.refl

/-- Naive fraction equivalence is symmetric. -/
theorem eqv_symm {p q : Naive.Fraction ℤ} : p ≃ q → q ≃ p := by
  revert p; intro (a//b); revert q; intro (c//d)
  intro (_ : a//b ≃ c//d)
  show c//d ≃ a//b
  have : a * d ≃ c * b := ‹a//b ≃ c//d›
  show c * b ≃ a * d
  exact Rel.symm ‹a * d ≃ c * b›

/--
The transitive property fails for "equivalence" on naive fractions.

**Proof intuition**: We assume transitivity holds and show that it leads to a
contradiction. Define fractions `p` and `r` such that `p ≄ r`. Define `q` to be
the fraction `0//0`, and note that `p ≃ q` and `q ≃ r`. Now invoke transitivity
to show that `p ≃ r`, contradicting our definition of `p` and `r`.
-/
theorem eqv_trans_impossible
    : ¬(∀ p q r : Naive.Fraction ℤ, p ≃ q → q ≃ r → p ≃ r)
    := by
  intro (trans : {p q r : Naive.Fraction ℤ} → p ≃ q → q ≃ r → p ≃ r)
  show False
  let p : Naive.Fraction ℤ := 1//0
  let q : Naive.Fraction ℤ := 0//0
  let r : Naive.Fraction ℤ := 1//1
  have : p ≃ q := by
    show 1//0 ≃ 0//0
    show 1 * 0 ≃ 0 * 0
    calc
      (1 : ℤ) * 0 ≃ _ := AA.absorbR
      0           ≃ _ := Rel.symm AA.absorbR
      0 * 0       ≃ _ := Rel.refl
  have : q ≃ r := by
    show 0//0 ≃ 1//1
    show 0 * 1 ≃ 1 * 0
    exact AA.comm
  have : p ≄ r := by
    intro (_ : p ≃ r)
    show False
    have : (1 : ℤ)//0 ≃ 1//1 := ‹p ≃ r›
    have : (1 : ℤ) * 1 ≃ 1 * 0 := ‹(1 : ℤ)//0 ≃ 1//1›
    have : (1 : ℤ) ≃ 0 := calc
      (1 : ℤ) ≃ _ := Rel.symm AA.identR
      1 * 1   ≃ _ := ‹(1 : ℤ) * 1 ≃ 1 * 0›
      1 * 0   ≃ _ := AA.absorbR
      0       ≃ _ := Rel.refl
    have : (1 : ℤ) ≄ 0 := Integer.one_neqv_zero
    exact absurd ‹(1 : ℤ) ≃ 0› ‹(1 : ℤ) ≄ 0›
  have : p ≃ r := trans ‹p ≃ q› ‹q ≃ r›
  exact absurd ‹p ≃ r› ‹p ≄ r›

/-!
Although general transitivity is impossible, by imposing some restrictions we
can prove it. For example, the usual approach of having a nonzero denominator:
-/

/--
Transitivity holds for naive fractions if the middle fraction's denominator is
nonzero.

**Proof intuition**: Using the `p ≃ q` and `q ≃ r` hypotheses, we can almost
show `p ≃ r` -- except that both sides of the equivalence have an extra factor
of `q.denominator`. We're allowed to cancel it out because of the assumption
that it's nonzero.
-/
theorem eqv_trans_nonzero_denom
    {p q r : Naive.Fraction ℤ} : q.denominator ≄ 0 → p ≃ q → q ≃ r → p ≃ r
    := by
  revert p; intro (pn//pd); revert q; intro (qn//qd); revert r; intro (rn//rd)
  intro (_ : qd ≄ 0) (_ : pn//pd ≃ qn//qd) (_ : qn//qd ≃ rn//rd)
  show pn//pd ≃ rn//rd
  have : (pn * rd) * qd ≃ (rn * pd) * qd := calc
    (pn * rd) * qd ≃ _ := AA.substL AA.comm
    (rd * pn) * qd ≃ _ := AA.assoc
    rd * (pn * qd) ≃ _ := AA.substR ‹pn * qd ≃ qn * pd›
    rd * (qn * pd) ≃ _ := Rel.symm AA.assoc
    (rd * qn) * pd ≃ _ := AA.substL AA.comm
    (qn * rd) * pd ≃ _ := AA.substL ‹qn * rd ≃ rn * qd›
    (rn * qd) * pd ≃ _ := AA.assoc
    rn * (qd * pd) ≃ _ := AA.substR AA.comm
    rn * (pd * qd) ≃ _ := Rel.symm AA.assoc
    (rn * pd) * qd ≃ _ := Rel.refl
  have : pn * rd ≃ rn * pd :=
    Integer.mul_cancelR ‹qd ≄ 0› ‹(pn * rd) * qd ≃ (rn * pd) * qd›
  exact this

/-!
What exactly are the conditions under which transitivity on naive fractions is
possible? Looking back at the counterexample in the impossibility proof, the
key idea was setting `q := 0//0`. This forced `p ≃ q` and `q ≃ r` to hold, even
though `p ≄ r`. In fact, it looks as though the value `0//0` is equivalent to
_any_ naive fraction; let's prove it.
-/

/--
The naive fraction `0//0` is equivalent to any naive fraction.

**Proof intuition**: Expanding the definition of equivalence produces an
equivalence of two products, each containing a factor of zero. By absorption,
this is the same as `0 ≃ 0`, which is trivially true.
-/
theorem zero_over_zero_eqv_any {p : Naive.Fraction ℤ} : 0//0 ≃ p := by
  revert p; intro (pn//pd)
  show 0//0 ≃ pn//pd
  show 0 * pd ≃ pn * 0
  calc
    0 * pd ≃ _ := AA.absorbL
    0      ≃ _ := Rel.symm AA.absorbR
    pn * 0 ≃ _ := Rel.refl

/-!
That result is certainly a disaster for creating a model of fractions that
matches our intuition. If every fraction is equivalent to `0//0`, then they are
all equivalent to each other, making them useless as numbers. Fortunately, it
turns out that disallowing `0//0` is the only thing we need to restore
transitivity of equivalence:
-/

/--
Transitivity holds for naive fractions when the middle fraction is not `0//0`.

**Proof intuition**: We already know transitivity holds when the middle
fraction's denominator is nonzero (see `eqv_trans_nonzero_denom`). When its
denominator is zero, the assumptions `p ≃ q` and `q ≃ r` imply that there are
two possibilities: either its numerator is also zero, or the denominators of
the other two fractions are zero. In the first case, the middle fraction is
`0//0`, and transitivity may fail. In the second case, `p ≃ r` reduces to
`0 ≃ 0` because `p` and `r`'s denominators are zero, and transitivity holds.
-/
theorem eqv_trans_almost
    {p q r : Naive.Fraction ℤ}
    : p ≃ q → q ≃ r → (p ≃ r ∨ q.to_prod ≃ (0//0).to_prod)
    := by
  revert p; intro (pn//pd); revert q; intro (qn//qd); revert r; intro (rn//rd)
  intro (_ : pn//pd ≃ qn//qd) (_ : qn//qd ≃ rn//rd)
  show pn//pd ≃ rn//rd ∨ (qn//qd).to_prod ≃ (0//0).to_prod
  show pn * rd ≃ rn * pd ∨ (qn, qd) ≃ (0, 0)
  have : Decidable (qd ≃ 0) := Integer.eqv? qd 0
  match this with
  | isTrue (_ : qd ≃ 0) =>
    have : pn * qd ≃ qn * pd := ‹pn//pd ≃ qn//qd›
    have : qn * rd ≃ rn * qd := ‹qn//qd ≃ rn//rd›
    have : qn * pd ≃ 0 := calc
      qn * pd ≃ _ := Rel.symm ‹pn * qd ≃ qn * pd›
      pn * qd ≃ _ := AA.substR ‹qd ≃ 0›
      pn * 0  ≃ _ := AA.absorbR
      0       ≃ _ := Rel.refl
    have : qn * rd ≃ 0 := calc
      qn * rd ≃ _ := ‹qn * rd ≃ rn * qd›
      rn * qd ≃ _ := AA.substR ‹qd ≃ 0›
      rn * 0  ≃ _ := AA.absorbR
      0       ≃ _ := Rel.refl
    have : qn ≃ 0 ∨ pd ≃ 0 := Integer.mul_split_zero.mp ‹qn * pd ≃ 0›
    have : qn ≃ 0 ∨ rd ≃ 0 := Integer.mul_split_zero.mp ‹qn * rd ≃ 0›
    have : (qn ≃ 0 ∨ pd ≃ 0) ∧ (qn ≃ 0 ∨ rd ≃ 0) :=
      And.intro ‹qn ≃ 0 ∨ pd ≃ 0› ‹qn ≃ 0 ∨ rd ≃ 0›
    have : qn ≃ 0 ∨ (pd ≃ 0 ∧ rd ≃ 0) :=
      Logic.or_distribL_and.mpr ‹(qn ≃ 0 ∨ pd ≃ 0) ∧ (qn ≃ 0 ∨ rd ≃ 0)›
    match ‹qn ≃ 0 ∨ (pd ≃ 0 ∧ rd ≃ 0)› with
    | Or.inl (_ : qn ≃ 0) =>
      have : qn ≃ 0 ∧ qd ≃ 0 := And.intro ‹qn ≃ 0› ‹qd ≃ 0›
      have : (qn, qd) ≃ (0, 0) :=
        Relation.Equivalence.Impl.Prod.eqv_defn.mpr ‹qn ≃ 0 ∧ qd ≃ 0›
      exact Or.inr ‹(qn, qd) ≃ (0, 0)›
    | Or.inr (And.intro (_ : pd ≃ 0) (_ : rd ≃ 0)) =>
      have : pn * rd ≃ rn * pd := calc
        pn * rd ≃ _ := AA.substR ‹rd ≃ 0›
        pn * 0  ≃ _ := AA.absorbR
        0       ≃ _ := Rel.symm AA.absorbR
        rn * 0  ≃ _ := AA.substR (Rel.symm ‹pd ≃ 0›)
        rn * pd ≃ _ := Rel.refl
      exact Or.inl ‹pn * rd ≃ rn * pd›
  | isFalse (_ : qd ≄ 0) =>
    have : pn * rd ≃ rn * pd :=
      eqv_trans_nonzero_denom
        (q := qn//qd)
        ‹qd ≄ 0›
        ‹pn//pd ≃ qn//qd›
        ‹qn//qd ≃ rn//rd›
    exact Or.inl ‹pn * rd ≃ rn * pd›

/-!
So all we need to do to have useful fractions is disallow the value `0//0`? Not
quite. So far, all of the operations we've defined on naive fractions have put
the numerator and denominator on equal footing; we could swap them and all our
results would still be valid.

Addition of fractions breaks this symmetry. It requires one of the two
components to measure "quantity" (the numerator) and the other to measure
"scale" (the denominator). The choice is arbitrary, but it must be consistent.

Any sensible definition of fractions needs to support a quantity of zero, at
all possible scales. Thus the numerator must be allowed to become zero. But in
order to prevent the `0//0` case, the simplest thing to do is require that the
denominator is never zero. Fortunately, the natural definition of addition
already does this, as we'll soon see.
-/

/--
Addition of naive integer fractions.

**Intuition**: Similar to the definition of equivalence, our informal
justification is that fractions represent a division operation, which is undone
via multiplication. Also, fractions represent an integer quantity (the
numerator) that has been scaled down in size by an integer factor (the
denominator). If two fractions have the same denominator, their numerators are
"at the same scale" and can thus be added directly.

Those principles lead to the following chain of equivalent expressions, that
provide a reason for our definition of addition:
1. `a//b + c//d`
2. `(a//b) * 1 + 1 * (c//d)`
3. `(a//b) * (d//d) + (b//b) * (c//d)`
4. `(a * d)//(b * d) + (b * c)//(b * d)`
5. `(a * d + b * c)//(b * d)`
-/
def add : Naive.Fraction ℤ → Naive.Fraction ℤ → Naive.Fraction ℤ
| a//b, c//d => (a * d + b * c)//(b * d)

/-- Provide the `· + ·` operator for addition of naive fractions. -/
instance addOp : Add (Naive.Fraction ℤ) := {
  add := add
}

/--
As mentioned above, we cannot avoid having zero-valued numerators if we have
addition of fractions. Here's one example where fractions having nonzero
components produce a numerator with value zero when added.
-/
example : (2//4 + (-1 : ℤ)//2).numerator ≃ 0 := by
  show 2 * 2 + 4 * -1 ≃ 0
  calc
    2 * 2 + 4 * (-1 : ℤ)
      ≃ _ := AA.substR (Rel.symm AA.scompatR)
    2 * 2 + -(4 * 1)
      ≃ _ := AA.substR (AA.subst₁ AA.identR)
    2 * 2 + -4
      ≃ _ := Rel.refl
    coe 2 * coe 2 + -4
      ≃ _ := AA.substL (Rel.symm AA.compat₂)
    coe (2 * 2) + -4
      ≃ _ := AA.substL (AA.subst₁ (AA.substL Natural.literal_step))
    coe (step 1 * 2) + -4
      ≃ _ := AA.substL (AA.subst₁ Natural.step_mul)
    coe (1 * 2 + 2) + -4
      ≃ _ := AA.substL (AA.subst₁ (AA.substL AA.identL))
    coe (2 + 2) + -4
      ≃ _ := AA.substL (AA.subst₁ (AA.substL Natural.literal_step))
    coe (step 1 + 2) + -4
      ≃ _ := AA.substL (AA.subst₁ Natural.step_add_swap)
    coe (1 + step 2) + -4
      ≃ _ := AA.substL (AA.subst₁ (AA.substL Natural.literal_step))
    coe (step 0 + step 2) + -4
      ≃ _ := AA.substL (AA.subst₁ Natural.step_add_swap)
    coe (0 + step (step 2)) + -4
      ≃ _ := AA.substL (AA.subst₁ AA.identL)
    coe (step (step 2)) + -4
      ≃ _ := AA.substL (AA.subst₁ (AA.subst₁ (Rel.symm Natural.literal_step)))
    coe (step 3) + -4
      ≃ _ := AA.substL (AA.subst₁ (Rel.symm Natural.literal_step))
    coe 4 + -4
      ≃ _ := Rel.refl
    4 + -4
      ≃ _ := AA.inverseR
    0
      ≃ _ := Rel.refl

/--
Adding two naive fractions with zero-valued denominators always gives `0//0`.

One might hope that there are cases where adding fractions with zero-valued
denominators can make sense, but this proof shows that's not possible. In fact,
even if only one operand's denominator is zero, it can be seen from the proof
that the result's denominator will still be zero. Thus in any expression adding
naive fractions, if there are just two denominators that are zero, the entire
sum will always reduce to `0//0`, a useless result.

**Proof intuition**: Handle the numerator and the denominator separately. The
numerator becomes zero because it's a sum of two products, where each of them
has a zero-valued denominator as one of the factors. The denominator is zero
because both of its factors are zero.
-/
theorem add_zero_denominators
    {a b : ℤ} : (a//0 + b//0).to_prod ≃ (0//0).to_prod
    := by
  show ((a * 0 + 0 * b)//(0 * 0)).to_prod ≃ (0//0).to_prod
  show (a * 0 + 0 * b, 0 * 0) ≃ (0, 0)
  apply Relation.Equivalence.Impl.Prod.eqv_defn.mpr
  show a * 0 + 0 * b ≃ 0 ∧ 0 * 0 ≃ 0
  apply And.intro
  case left =>
    show a * 0 + 0 * b ≃ 0
    calc
      a * 0 + 0 * b ≃ _ := AA.substL AA.absorbR
      0 + 0 * b     ≃ _ := AA.identL
      0 * b         ≃ _ := AA.absorbL
      0             ≃ _ := Rel.refl
  case right =>
    show 0 * 0 ≃ 0
    exact AA.absorbL

/--
Adding two naive fractions with nonzero denominators always gives a result with
a nonzero denominator.

This result enables us to ban fractions with zero-valued denominators: they can
never be produced as long as we always start with nonzero denominators.

**Proof intuition**: The denominator of a sum of fractions is the product of
the denominators of those fractions. And the product of two nonzero integers is
always nonzero.
-/
theorem add_preserves_nonzero_denominators
    {p q : Naive.Fraction ℤ}
    : Nonzero p.denominator → Nonzero q.denominator
    → Nonzero ((p + q).denominator)
    := by
  revert p; intro (pn//pd); revert q; intro (qn//qd)
  intro (_ : Nonzero pd) (_ : Nonzero qd)
  show Nonzero (pn//pd + qn//qd).denominator
  show Nonzero ((pn * qd + pd * qn)//(pd * qd)).denominator
  show Nonzero (pd * qd)
  exact Integer.mul_preserves_nonzero ‹Nonzero pd› ‹Nonzero qd›

/-!
In summary, if we want to have meaningful equivalence between fractions, we
cannot allow them to have the value `0//0`. But that's not quite enough; if we
allow zero-valued denominators with nonzero numerators, addition of fractions
will inevitably give `0//0` results. Thus there's only one possible option:
we can allow zero-valued numerators, but denominators must always be nonzero.
-/

/--
Adding two naive fractions with positive denominators always gives a result
with a positive denominator.

This is an alternative to the nonzero-denominators approach above, which is in
some ways nicer because it restricts negative values to the numerator only. The
sign of the fraction is then fully determined by the numerator, while the
denominator's only role is to represent the size of the numerator's units.

**Proof intuition**: The denominator of a sum of fractions is the product of
the denominators of those fractions. And the product of two positive integers
is always positive.
-/
theorem add_preserves_positive_denominators
    {p q : Naive.Fraction ℤ}
    : Positive p.denominator → Positive q.denominator
    → Positive ((p + q).denominator)
    := by
  revert p; intro (pn//pd); revert q; intro (qn//qd)
  intro (_ : Positive pd) (_ : Positive qd)
  show Positive (pn//pd + qn//qd).denominator
  show Positive ((pn * qd + pd * qn)//(pd * qd)).denominator
  show Positive (pd * qd)
  exact Integer.mul_preserves_positive ‹Positive pd› ‹Positive qd›

end Lean4Axiomatic.Rational.Impl.Fraction.Naive
