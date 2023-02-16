import Lean4Axiomatic.Integer.Negation
import Lean4Axiomatic.Logic
import Lean4Axiomatic.Sign

/-!
# Integer signedness
-/

namespace Lean4Axiomatic.Integer

open Coe (coe)
open Logic (AP)
open Signed (Negative Positive)

/-!
## Preliminary definitions and theorems
-/

section prelim

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core (ℕ := ℕ) ℤ]
variable [Addition ℤ] [Multiplication ℤ] [Negation ℤ]

/--
Square root of unity: an integer whose square is one.

Only `1` and `-1` satisfy this property. This makes it useful for indicating
when an integer is a "pure sign"; that is, a positive or negative integer of
unit magnitude. Pure signs can be multiplied by positive integers to produce
any nonzero integer.

This property is easy to work with algebraically because it uses
multiplication.

**Named parameters**
- `a`: The integer satisfying the property.
-/
class Sqrt1 (a : ℤ) : Prop :=
  /-- The underlying property expressed by `Sqrt1`. -/
  elim : a * a ≃ 1

/--
The `Sqrt1` predicate respects equivalence.

**Property intuition**: This must be true for `Sqrt1` to make sense as a
predicate.

**Proof intuition**: Expand the definition of `Sqrt1` to obtain an equivalence
involving multiplication. Since multiplication is substitutive, the result
follows easily.
-/
theorem sqrt1_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → Sqrt1 a₁ → Sqrt1 a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : Sqrt1 a₁)
  show Sqrt1 a₂
  have : a₂ * a₂ ≃ 1 := calc
    a₂ * a₂ ≃ _ := AA.substL (Rel.symm ‹a₁ ≃ a₂›)
    a₁ * a₂ ≃ _ := AA.substR (Rel.symm ‹a₁ ≃ a₂›)
    a₁ * a₁ ≃ _ := ‹Sqrt1 a₁›.elim
    1       ≃ _ := Rel.refl
  exact Sqrt1.mk ‹a₂ * a₂ ≃ 1›

instance sqrt1_substitutive
    : AA.Substitutive₁ (α := ℤ) Sqrt1 (· ≃ ·) (· → ·)
    := {
  subst₁ := sqrt1_subst
}

/-- One is a square root of unity. -/
theorem one_mul_one_eqv_one : (1 : ℤ) * 1 ≃ 1 := by
  show 1 * 1 ≃ 1
  exact AA.identL

instance sqrt1_one : Sqrt1 (1 : ℤ) := {
  elim := one_mul_one_eqv_one
}

/--
Negative one is a square root of unity.

**Property and proof intuition**: Multiplying two negative numbers gives a
positive result, and if the magnitudes are `1`, the result will also be `1`.
-/
theorem neg_one_mul_neg_one_eqv_one : (-1 : ℤ) * (-1) ≃ 1 := by
  calc
    (-1 : ℤ) * (-1) ≃ _ := Rel.symm AA.scompatL
    (-(1 * (-1)))   ≃ _ := AA.subst₁ (Rel.symm AA.scompatR)
    (-(-(1 * 1)))   ≃ _ := neg_involutive
    1 * 1           ≃ _ := one_mul_one_eqv_one
    1               ≃ _ := Rel.refl

instance sqrt1_neg_one : Sqrt1 (-1 : ℤ) := {
  elim := neg_one_mul_neg_one_eqv_one
}

/--
The product of square roots of unity is also a square root of unity.

This is an important result; it means that positive and negative signs can be
represented by integers, allowing derivations using algebra.

**Property intuition**: A factor of `1` or `-1` in a product does not change
the magnitude of the result. Thus, regardless of the signs involved, a product
of two square roots of unity can only be `1` or `-1`.

**Proof intuition**: Rearrange factors with associativity to isolate `a` and
`b` into products with themselves. By the definition of `Sqrt1`, those products
must each be `1`; thus the product of the products is also `1`.
-/
instance mul_preserves_sqrt1
    {a b : ℤ} [Sqrt1 a] [Sqrt1 b] : Sqrt1 (a * b)
    := by
  apply Sqrt1.mk
  show (a * b) * (a * b) ≃ 1
  calc
    (a * b) * (a * b) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (a * a) * (b * b) ≃ _ := AA.substL ‹Sqrt1 a›.elim
    1 * (b * b)       ≃ _ := AA.substR ‹Sqrt1 b›.elim
    1 * 1             ≃ _ := one_mul_one_eqv_one
    1                 ≃ _ := Rel.refl

/--
The negation of a square root of unity is also a square root of unity.

**Property intuition**: Squaring removes negation, so anything that results in
one when squared will give the same result even if negated.

**Proof intuition**: Negation is the same as multiplication by -1. Since -1 is
a square root of unity, the result follows because a product of square roots of
unity is also a square root of unity.
-/
instance neg_preserves_sqrt1 {a : ℤ} [Sqrt1 a] : Sqrt1 (-a) := by
  have : Sqrt1 (-1 * a) := inferInstance
  have : Sqrt1 (-a) := AA.substFn mul_neg_one ‹Sqrt1 (-1 * a)›
  exact this

/--
Demonstrates that a nonzero integer can be factored into _sign_ and _magnitude_
components.

The sign value is either positive (represented by `1`) or negative (represented
by `-1`). The magnitude must be a positive natural number.

This data structure is a foundation for defining the `Positive`, `Negative`,
and `Nonzero` predicates on integers. It can be easier to work with than those,
because it represents positive and negative numbers in a uniform way that's
suited to algebraic operations.

**Parameters**
- `a`: The nonzero integer to represent in signed-magnitude form.
- `s`: The sign value.
- `sqrt1`: Ensures that `s` is either `1` or `-1`.
-/
inductive NonzeroWithSign (a : ℤ) (s : ℤ) [sqrt1 : Sqrt1 s] : Prop
| /--
  Construct evidence that the integer `a` is nonzero, with sign component `s`.

  **Parameters**
  - `m`: The magnitude value.
  - `pos`: Ensures a positive magnitude.
  - `eqv`: Proof that `a` is a product of the sign and the magnitude.
  -/
  intro (m : ℕ) (pos : Positive m) (eqv : a ≃ s * coe m)

/--
A pure sign (i.e., a square root of unity) is its own sign value.

**Intuition**: Set the magnitude component of `NonzeroWithSign` to one.
-/
def NonzeroWithSign.for_sign {s : ℤ} [Sqrt1 s] : NonzeroWithSign s s :=
  have : Positive 1 := Natural.one_positive
  have : s ≃ s * 1 := Rel.symm AA.identR
  NonzeroWithSign.intro (1 : ℕ) ‹Positive (1 : ℕ)› ‹s ≃ s * 1›

/--
`NonzeroWithSign` respects equivalence of its nonzero integer parameter.

**Property intuition**: This is necessary for `NonzeroWithSign` to be a valid
predicate.

**Proof intuition**: The underlying relation for `NonzeroWithSign` is
equivalence, so replacing `a₁` with `a₂` follows from transitivity.
-/
theorem NonzeroWithSign.subst_nonzero
    {a₁ a₂ s : ℤ} {_ : Sqrt1 s}
    : a₁ ≃ a₂ → NonzeroWithSign a₁ s → NonzeroWithSign a₂ s
    := by
  intro (_ : a₁ ≃ a₂)
  intro (NonzeroWithSign.intro (m : ℕ) (_ : Positive m) (_ : a₁ ≃ s * coe m))
  show NonzeroWithSign a₂ s
  have : a₂ ≃ s * coe m := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ s * coe m›
  exact NonzeroWithSign.intro m ‹Positive m› ‹a₂ ≃ s * coe m›

/--
`NonzeroWithSign` respects equivalence of signs.

**Property intuition**: If signs `s₁` and `s₂` are equivalent, and we have a
`NonzeroWithSign` for `s₁`, then that can be converted into a `NonzeroWithSign`
for `s₂`. This _must_ be true for `NonzeroWithSign` to be a valid predicate.

**Proof intuition**: Extract the equivalence for `s₁`, substitute `s₂` into it,
and build a new `NonzeroWithSign` on `s₂`.
-/
theorem NonzeroWithSign.subst_sign
    {a s₁ s₂ : ℤ} {_ : Sqrt1 s₁} {_ : Sqrt1 s₂} (_ : s₁ ≃ s₂)
    : NonzeroWithSign a s₁ → NonzeroWithSign a s₂
    := by
  intro (NonzeroWithSign.intro (m : ℕ) (_ : Positive m) (_ : a ≃ s₁ * coe m))
  have : a ≃ s₂ * coe m := Rel.trans ‹a ≃ s₁ * coe m› (AA.substL ‹s₁ ≃ s₂›)
  exact NonzeroWithSign.intro m ‹Positive m› ‹a ≃ s₂ * coe m›

/--
Given two integers in signed-magnitude form, we can put their product in
signed-magnitude form as well.

**Property intuition**: This seems plausible, if only because every integer can
be put into signed-magnitude form.

**Proof intuition**: From previous results, we know that multiplication
preserves `Sqrt1` and `Positive` on natural numbers. Then we just need to show
that the product of two signed-magnitude forms can itself be put into
signed-magnitude form; this follows mostly from algebra on multiplication.
-/
theorem mul_preserves_nonzeroWithSign
    {a b as bs : ℤ} {a_sqrt1 : Sqrt1 as} {b_sqrt1 : Sqrt1 bs}
    : NonzeroWithSign a as → NonzeroWithSign b bs
    → NonzeroWithSign (a * b) (as * bs)
    := by
  intro
    (NonzeroWithSign.intro (am : ℕ) (_ : Positive am) (_ : a ≃ as * coe am))
  intro
    (NonzeroWithSign.intro (bm : ℕ) (_ : Positive bm) (_ : b ≃ bs * coe bm))
  show NonzeroWithSign (a * b) (as * bs)
  have : Positive (am * bm) := Natural.mul_positive ‹Positive am› ‹Positive bm›
  have : a * b ≃ (as * bs) * coe (am * bm) := calc
    a * b                         ≃ _ := AA.substL ‹a ≃ as * coe am›
    (as * coe am) * b             ≃ _ := AA.substR ‹b ≃ bs * coe bm›
    (as * coe am) * (bs * coe bm) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (as * bs) * (coe am * coe bm) ≃ _ := AA.substR (Rel.symm AA.compat₂)
    (as * bs) * coe (am * bm)     ≃ _ := Rel.refl
  exact NonzeroWithSign.intro
    (am * bm) ‹Positive (am * bm)› ‹a * b ≃ (as * bs) * coe (am * bm)›

/--
Negation can be exchanged between the value and the sign of `NonzeroWithSign`.

**Property intuition**: If `-a` has sign `s`, then `a` must have the opposite
sign `-s`.

**Proof intuition**: Expand the definition of `NonzeroWithSign` and perform
some algebra on the equivalence involving `a` and `s`.
-/
theorem nonzeroWithSign_swap_neg
    {a s : ℤ} {_ : Sqrt1 s} : NonzeroWithSign (-a) s ↔ NonzeroWithSign a (-s)
    := by
  apply Iff.intro
  case mp =>
    intro (NonzeroWithSign.intro (n : ℕ) (_ : Positive n) (_ : -a ≃ s * coe n))
    show NonzeroWithSign a (-s)
    have : a ≃ -s * coe n := calc
      a              ≃ _ := Rel.symm neg_involutive
      (-(-a))        ≃ _ := AA.subst₁ ‹-a ≃ s * coe n›
      (-(s * coe n)) ≃ _ := AA.scompatL
      (-s) * coe n   ≃ _ := Rel.refl
    exact NonzeroWithSign.intro n ‹Positive n› ‹a ≃ -s * coe n›
  case mpr =>
    intro (NonzeroWithSign.intro (n : ℕ) (_ : Positive n) (_ : a ≃ -s * coe n))
    show NonzeroWithSign (-a) s
    have : -a ≃ s * coe n := calc
      (-a)            ≃ _ := AA.subst₁ ‹a ≃ -s * coe n›
      (-(-s * coe n)) ≃ _ := AA.scompatL
      (-(-s)) * coe n ≃ _ := AA.substL neg_involutive
      s * coe n       ≃ _ := Rel.refl
    exact NonzeroWithSign.intro n ‹Positive n› ‹-a ≃ s * coe n›

/--
Evidence that an integer is not zero, with no other details.

Same as `NonzeroWithSign`, but the sign is a field instead of a parameter.

**Parameters**
- `a`: The integer that is not zero.
-/
class inductive Nonzero (a : ℤ) : Prop :=
| /--
  Construct evidence that the integer `a` is nonzero.

  **Parameters**
  - See `Nonzero` for the class-level parameters.
  - `sign`: Has value `1` if `a` is positive, or `-1` if `a` is negative.
  - `sqrt1`: Evidence that `sign` is `1` or `-1`.
  - `nws`: Evidence that `sign` is the sign of `a`.
  -/
  intro
    (sign : ℤ)
    (sqrt1 : Sqrt1 sign)
    (nws : NonzeroWithSign a sign)

/--
Convenience constructor that infers early arguments of `Nonzero.intro` from the
last, `NonzeroWithSign` argument.
-/
def Nonzero.mk {a s : ℤ} {sqrt1 : Sqrt1 s} : NonzeroWithSign a s → Nonzero a :=
  Nonzero.intro s sqrt1

/-- Sign values (i.e., square roots of unity) are nonzero. -/
instance nonzero_sqrt1 {s : ℤ} [Sqrt1 s] : Nonzero s :=
  Nonzero.mk NonzeroWithSign.for_sign

/--
The `Nonzero` predicate respects equivalence.

**Property intuition**: Necessary for `Nonzero` to be a valid predicate.

**Proof intuition**: Follows directly from substitution on `NonzeroWithSign`.
-/
theorem nonzero_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → Nonzero a₁ → Nonzero a₂ := by
  intro (_ : a₁ ≃ a₂) (Nonzero.intro (s : ℤ) (_ : Sqrt1 s) nws)
  have : NonzeroWithSign a₁ s := nws
  show Nonzero a₂
  have : NonzeroWithSign a₂ s :=
    NonzeroWithSign.subst_nonzero ‹a₁ ≃ a₂› ‹NonzeroWithSign a₁ s›
  exact Nonzero.mk ‹NonzeroWithSign a₂ s›

/--
The product of nonzero integers is nonzero.

**Property and proof intuition**: `Nonzero` can be decomposed into a sign value
and a `NonzeroWithSign` value. Previous results have shown that both of those
components are preserved under multiplication, so a `Nonzero` value for the
product of `Nonzero` integers can always be constructed.
-/
theorem mul_preserves_nonzero
    {a b : ℤ} : Nonzero a → Nonzero b → Nonzero (a * b)
    := by
  intro (Nonzero.intro as (_ : Sqrt1 as) nwsa)
  intro (Nonzero.intro bs (_ : Sqrt1 bs) nwsb)
  have : NonzeroWithSign a as := nwsa
  have : NonzeroWithSign b bs := nwsb
  show Nonzero (a * b)
  have : NonzeroWithSign (a * b) (as * bs) :=
    mul_preserves_nonzeroWithSign ‹NonzeroWithSign a as› ‹NonzeroWithSign b bs›
  exact Nonzero.mk ‹NonzeroWithSign (a * b) (as * bs)›

/-- Instance version of `mul_preserves_nonzero`. -/
instance mul_preserves_nonzero_inst
    {a b : ℤ} [Nonzero a] [Nonzero b] : Nonzero (a * b)
    :=
  mul_preserves_nonzero ‹Nonzero a› ‹Nonzero b›

/--
The negation of a nonzero integer is nonzero.

**Property intuition**: Negation only results in zero when the input is zero.

**Proof intuition**: Negation is equivalent to multiplication by `-1`, which is
a nonzero integer, so its product with the nonzero input is also nonzero.
-/
theorem neg_preserves_nonzero {a : ℤ} : Nonzero a → Nonzero (-a) := by
  intro (_ : Nonzero a)
  show Nonzero (-a)
  have : Nonzero (-1 : ℤ) := nonzero_sqrt1
  have : Nonzero (-1 * a) := mul_preserves_nonzero ‹Nonzero (-1 : ℤ)› ‹Nonzero a›
  have : Nonzero (-a) := nonzero_subst mul_neg_one ‹Nonzero (-1 * a)›
  exact this

/-- Instance version of `neg_preserves_nonzero`. -/
instance neg_preserves_nonzero_inst {a : ℤ} [Nonzero a] : Nonzero (-a) :=
  neg_preserves_nonzero ‹Nonzero a›

/--
Convert `Ordering` values into standard integer sign values.

Interprets the `Ordering` as being in relation to zero; e.g. `Ordering.lt` is
assigned `-1` because integers less than zero are negative.
-/
def ord_sgn : Ordering → ℤ
| Ordering.lt => -1
| Ordering.eq => 0
| Ordering.gt => 1

/--
The `ord_sgn` function produces a unique integer for every `Ordering` value.

**Property intuition**: All functions on `Ordering` automatically have this
property, because `Ordering` values can be compared for equality.

**Proof intuition**: Use substitution of equality to make the result follow
trivially from reflexivity of equivalence.
-/
theorem ord_sgn_subst
    {o₁ o₂ : Ordering} : o₁ = o₂ → ord_sgn o₁ ≃ ord_sgn (ℤ := ℤ) o₂
    := by
  intro (_ : o₁ = o₂)
  show ord_sgn o₁ ≃ ord_sgn o₂
  rw [‹o₁ = o₂›]
  show ord_sgn o₂ ≃ ord_sgn o₂
  exact Rel.refl

/--
Every integer result of the `ord_sgn` function is obtained from a unique
`Ordering` value.

**Property intuition**: This is because `ord_sgn` does not map two `Ordering`
values to the same integer.

**Proof intuition**: Follows by brute force: compare results of `ord_sgn` for
every possible pair of inputs. Show that the results are equivalent only when
the inputs are equal.
-/
theorem ord_sgn_inject
    : {o₁ o₂ : Ordering} → ord_sgn o₁ ≃ ord_sgn (ℤ := ℤ) o₂ → o₁ = o₂
| Ordering.lt, Ordering.lt, (_ : -1 ≃ (-1 : ℤ)) =>
  rfl
| Ordering.lt, Ordering.eq, (_ : -1 ≃ (0 : ℤ)) =>
  absurd (by assumption) neg_one_neqv_zero
| Ordering.lt, Ordering.gt, (_ : -1 ≃ (1 : ℤ)) =>
  absurd (by assumption) neg_one_neqv_one
| Ordering.eq, Ordering.lt, (_ : 0 ≃ (-1 : ℤ)) =>
  absurd (by assumption) (Rel.symm neg_one_neqv_zero)
| Ordering.eq, Ordering.eq, (_ : 0 ≃ (0 : ℤ)) =>
  rfl
| Ordering.eq, Ordering.gt, (_ : 0 ≃ (1 : ℤ)) =>
  absurd (by assumption) (Rel.symm one_neqv_zero)
| Ordering.gt, Ordering.lt, (_ : 1 ≃ (-1 : ℤ)) =>
  absurd (by assumption) (Rel.symm neg_one_neqv_one)
| Ordering.gt, Ordering.eq, (_ : 1 ≃ (0 : ℤ)) =>
  absurd (by assumption) one_neqv_zero
| Ordering.gt, Ordering.gt, (_ : 1 ≃ (1 : ℤ)) =>
  rfl

end prelim

/-!
## Axioms
-/

/-- Integer signedness properties. -/
class Sign.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ]
      [Signed.Ops ℤ]
    :=
  /-- An integer is positive iff it has sign `1`. -/
  positive_iff_sign_pos1 {a : ℤ} : Signed.Positive a ↔ NonzeroWithSign a 1

  /-- An integer is negative iff it has sign `-1`. -/
  negative_iff_sign_neg1 {a : ℤ} : Signed.Negative a ↔ NonzeroWithSign a (-1)

  /-- An integer is nonzero iff it satisfies `Integer.Nonzero`. -/
  nonzero_iff_nonzero_impl {a : ℤ} : Signed.Nonzero a ↔ Integer.Nonzero a

  /-- Every value is one, and only one, of zero, positive, or negative. -/
  sign_trichotomy
    (a : ℤ) : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a)

export Sign.Props (
  negative_iff_sign_neg1 nonzero_iff_nonzero_impl positive_iff_sign_pos1
  sign_trichotomy
)

/-- Operations pertaining to the _signum_ function. -/
class Sgn.Ops {ℤ : outParam Type} (α : Type) :=
  /--
  The [signum function](https://en.wikipedia.org/wiki/Sign_function).

  Returns `1`, `0`, or `-1` if the input is positive, zero, or negative,
  respectively.
  -/
  sgn : α → ℤ

export Sgn.Ops (sgn)

/-- Properties of the _signum_ function on integers. -/
class Sgn.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Signed.Ops ℤ] [Ops ℤ]
    :=
  /-- Zero is the only integer with sign value zero. -/
  sgn_zero {a : ℤ} : a ≃ 0 ↔ sgn a ≃ (0 : ℤ)

  /-- Only positive integers have sign value one. -/
  sgn_positive {a : ℤ} : Positive a ↔ sgn a ≃ 1

  /-- Only negative integers have sign value negative one. -/
  sgn_negative {a : ℤ} : Negative a ↔ sgn a ≃ -1

export Sgn.Props (sgn_negative sgn_positive sgn_zero)

/-- All integer signedness axioms. -/
class Sign
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core ℤ] [Addition ℤ] [Multiplication ℤ] [Negation (ℕ := ℕ) ℤ]
    :=
  toSignedOps : Signed.Ops ℤ
  toSignProps : Sign.Props ℤ
  toSgnOps : Sgn.Ops ℤ
  toSgnProps : Sgn.Props ℤ

attribute [instance] Sign.toSignedOps
attribute [instance] Sign.toSignProps
attribute [instance] Sign.toSgnOps
attribute [instance] Sign.toSgnProps

/-!
## Derived properties
-/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℤ] [Addition ℤ] [Multiplication (ℕ := ℕ) ℤ]
variable [Negation ℤ] [Sign ℤ]

/--
The `Positive` predicate respects equivalence.

**Property intuition**: This must be true for `Positive` to make sense as a
predicate.

**Proof intuition**: The definition of `Positive` is an equivalence between the
integer argument of the predicate and an expression. Since we also have an
equivalence for substitution, the result follows by transitivity.
-/
theorem positive_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → Positive a₁ → Positive a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : Positive a₁)
  show Positive a₂
  have (NonzeroWithSign.intro (m : ℕ) (_ : Positive m) (_ : a₁ ≃ 1 * ↑m)) :=
    positive_iff_sign_pos1.mp ‹Positive a₁›
  have : a₂ ≃ 1 * ↑m := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ 1 * ↑m›
  have : NonzeroWithSign a₂ 1 :=
    NonzeroWithSign.intro m ‹Positive m› ‹a₂ ≃ 1 * ↑m›
  have : Positive a₂ := positive_iff_sign_pos1.mpr ‹NonzeroWithSign a₂ 1›
  exact this

/--
The `Negative` predicate respects equivalence.

**Property intuition**: This must be true for `Negative` to make sense as a
predicate.

**Proof intuition**: The definition of `Negative` is an equivalence between the
integer argument of the predicate and an expression. Since we also have an
equivalence for substitution, the result follows by transitivity.
-/
theorem negative_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → Negative a₁ → Negative a₂ := by
  intro (_ : a₁ ≃ a₂) (_ : Negative a₁)
  show Negative a₂
  have (NonzeroWithSign.intro (m : ℕ) (_ : Positive m) (_ : a₁ ≃ -1 * ↑m)) :=
    negative_iff_sign_neg1.mp ‹Negative a₁›
  have : a₂ ≃ -1 * ↑m := Rel.trans (Rel.symm ‹a₁ ≃ a₂›) ‹a₁ ≃ -1 * ↑m›
  have : NonzeroWithSign a₂ (-1) :=
    NonzeroWithSign.intro m ‹Positive m› ‹a₂ ≃ -1 * ↑m›
  have : Negative a₂ := negative_iff_sign_neg1.mpr ‹NonzeroWithSign a₂ (-1)›
  exact this

/-- An integer is positive if it's equivalent to a positive natural number. -/
def positive_intro_nat
    {m : ℕ} {a : ℤ} : Positive m → a ≃ coe m → Positive a
    := by
  intro (_ : Positive m) (_ : a ≃ coe m)
  show Positive a
  have : a ≃ 1 * coe m := Rel.trans ‹a ≃ coe m› (Rel.symm AA.identL)
  have : NonzeroWithSign a 1 :=
    NonzeroWithSign.intro m ‹Positive m› ‹a ≃ 1 * coe m›
  exact positive_iff_sign_pos1.mpr ‹NonzeroWithSign a 1›

/--
The integer `1` is positive.

**Proof intuition**: Carry over the equivalent proof for natural numbers.
-/
theorem one_positive : Positive (1 : ℤ) :=
  have : (1 : ℤ) ≃ coe (1 : ℕ) := Rel.refl
  positive_intro_nat Natural.one_positive ‹(1 : ℤ) ≃ coe (1 : ℕ)›

/-- Make `one_positive` available for instance search. -/
instance one_positive_inst : AP (Positive (1 : ℤ)) := AP.mk one_positive

/--
Extract evidence that a positive integer is equivalent to a positive natural
number.
-/
def positive_elim_nat
    {a : ℤ} : Positive a → ∃ n : ℕ, Positive n ∧ a ≃ coe n
    := by
  intro (_ : Positive a)
  show ∃ n, Positive n ∧ a ≃ coe n
  have (NonzeroWithSign.intro (n : ℕ) (_ : Positive n) (_ : a ≃ 1 * coe n)) :=
    positive_iff_sign_pos1.mp ‹Positive a›
  have : a ≃ coe n := Rel.trans ‹a ≃ 1 * coe n› AA.identL
  exact Exists.intro n (And.intro ‹Positive n› ‹a ≃ coe n›)

/--
An integer is negative if it's equivalent to the negation of a positive natural
number.
-/
def negative_intro_nat
    {m : ℕ} {a : ℤ} : Positive m → a ≃ -(coe m) → Negative a
    := by
  intro (_ : Positive m) (_ : a ≃ -(coe m))
  show Negative a
  have : a ≃ -1 * coe m := Rel.trans ‹a ≃ -(coe m)› (Rel.symm mul_neg_one)
  have : NonzeroWithSign a (-1) :=
    NonzeroWithSign.intro m ‹Positive m› ‹a ≃ -1 * coe m›
  exact negative_iff_sign_neg1.mpr ‹NonzeroWithSign a (-1)›

/--
Extract evidence that a negative integer is equivalent to the negation of a
positive natural number.
-/
def negative_elim_nat
    {a : ℤ} : Negative a → ∃ n : ℕ, Positive n ∧ a ≃ -(coe n)
    := by
  intro (_ : Negative a)
  show ∃ n, Positive n ∧ a ≃ -(coe n)
  have (NonzeroWithSign.intro (n : ℕ) (_ : Positive n) (_ : a ≃ -1 * coe n)) :=
    negative_iff_sign_neg1.mp ‹Negative a›
  have : a ≃ -(coe n) := Rel.trans ‹a ≃ -1 * coe n› mul_neg_one
  exact Exists.intro n (And.intro ‹Positive n› ‹a ≃ -(coe n)›)

/--
Negative one (the negation of one) is a negative integer.

**Proof intuition**: A negative integer is the negation of a positive natural
number, in this case one.
-/
theorem neg_one_negative : Negative (-1 : ℤ) := by
  have : Positive (1 : ℕ) := Natural.one_positive
  have : (-1 : ℤ) ≃ -(coe (1 : ℕ)) := Rel.refl
  have : Negative (-1) :=
    negative_intro_nat ‹Positive (1 : ℕ)› ‹(-1 : ℤ) ≃ -(coe (1 : ℕ))›
  exact this

/-- Corollary of trichotomy that saves space in proofs. -/
theorem not_positive_and_negative {a : ℤ} : ¬(Positive a ∧ Negative a) := by
  intro (And.intro (_ : Positive a) (_ : Negative a))
  have two : AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a) :=
    AA.TwoOfThree.twoAndThree ‹Positive a› ‹Negative a›
  have not_two : ¬ AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a) :=
    (sign_trichotomy a).atMostOne
  exact absurd two not_two

/--
The only square roots of unity in the integers are `1` and `-1`.

**Property and proof intuition**: This follows from similar reasoning as
`Natural.sqrt1`. Zero squared is zero, and integers greater than one or less
than negative one all have squares that are greater than one.
-/
theorem sqrt1_cases {a : ℤ} : Sqrt1 a ↔ a ≃ 1 ∨ a ≃ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : Sqrt1 a)
    show a ≃ 1 ∨ a ≃ -1
    match (sign_trichotomy a).atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      apply False.elim
      show False
      have : (1 : ℤ) ≃ 0 := calc
        1     ≃ _ := Rel.symm ‹Sqrt1 a›.elim
        a * a ≃ _ := AA.substL ‹a ≃ 0›
        0 * a ≃ _ := AA.absorbL
        0     ≃ _ := Rel.refl
      exact absurd ‹(1 : ℤ) ≃ 0› one_neqv_zero
    | AA.OneOfThree.second (_ : Positive a) =>
      apply Or.inl
      show a ≃ 1
      have (Exists.intro (n : ℕ) (And.intro _ (_ : a ≃ (n : ℤ)))) :=
        positive_elim_nat ‹Positive a›
      have : ((n * n : ℕ) : ℤ) ≃ (1 : ℤ) := calc
        ((n * n : ℕ) : ℤ) ≃ _ := AA.compat₂
        (n : ℤ) * (n : ℤ) ≃ _ := AA.substL (Rel.symm ‹a ≃ (n : ℤ)›)
        a * (n : ℤ)       ≃ _ := AA.substR (Rel.symm ‹a ≃ (n : ℤ)›)
        a * a             ≃ _ := ‹Sqrt1 a›.elim
        1                 ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹((n * n : ℕ) : ℤ) ≃ (1 : ℤ)›
      have : n ≃ 1 := Natural.sqrt1.mp ‹n * n ≃ 1›
      show a ≃ 1
      calc
        a       ≃ _ := ‹a ≃ (n : ℤ)›
        (n : ℤ) ≃ _ := AA.subst₁ ‹n ≃ 1›
        (1 : ℤ) ≃ _ := Rel.refl
        (1 : ℤ) ≃ _ := Rel.refl
    | AA.OneOfThree.third (_ : Negative a) =>
      apply Or.inr
      show a ≃ -1
      have (Exists.intro (n : ℕ) (And.intro _ (_ : a ≃ -(n : ℤ)))) :=
        negative_elim_nat ‹Negative a›
      have : ((n * n : ℕ) : ℤ) ≃ (1 : ℤ) := calc
        ((n * n : ℕ) : ℤ)         ≃ _ := AA.compat₂
        (n : ℤ) * (n : ℤ)         ≃ _ := Rel.symm neg_involutive
        (-(-((n : ℤ) * (n : ℤ)))) ≃ _ := AA.subst₁ AA.scompatR
        (-((n : ℤ) * -(n : ℤ)))   ≃ _ := AA.scompatL
        (-(n : ℤ)) * (-(n : ℤ))   ≃ _ := AA.substL (Rel.symm ‹a ≃ -(n : ℤ)›)
        a * (-(n : ℤ))            ≃ _ := AA.substR (Rel.symm ‹a ≃ -(n : ℤ)›)
        a * a                     ≃ _ := ‹Sqrt1 a›.elim
        1                         ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹((n * n : ℕ) : ℤ) ≃ (1 : ℤ)›
      have : n ≃ 1 := Natural.sqrt1.mp ‹n * n ≃ 1›
      show a ≃ -1
      calc
        a          ≃ _ := ‹a ≃ -(n : ℤ)›
        (-(n : ℤ)) ≃ _ := AA.subst₁ (AA.subst₁ ‹n ≃ 1›)
        (-(1 : ℤ)) ≃ _ := Rel.refl
        (-1)       ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ 1 ∨ a ≃ -1)
    show Sqrt1 a
    match ‹a ≃ 1 ∨ a ≃ -1› with
    | Or.inl (_ : a ≃ 1) =>
      have : Sqrt1 (1 : ℤ) := sqrt1_one
      have : Sqrt1 a := AA.substFn (Rel.symm ‹a ≃ 1›) ‹Sqrt1 (1 : ℤ)›
      exact this
    | Or.inr (_ : a ≃ -1) =>
      have : Sqrt1 (-1 : ℤ) := sqrt1_neg_one
      have : Sqrt1 a := AA.substFn (Rel.symm ‹a ≃ -1›) ‹Sqrt1 (-1 : ℤ)›
      exact this

/--
The product of two square roots of unity is one iff they are the same.

**Property intuition**: It's an often-memorized algebraic fact that like signs
are the only ones whose product is positive.

**Proof intuition**: In the forward direction, there are two cases, `b ≃ 1` and
`b ≃ -1`. Show via algebra that `a ≃ b` in each. In the reverse direction,
substitute `b` for `a` and use the definition of square root of unity.
-/
theorem mul_sqrt1_eqv {a b : ℤ} [Sqrt1 b] : a * b ≃ 1 ↔ a ≃ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a * b ≃ 1)
    show a ≃ b
    have : b ≃ 1 ∨ b ≃ -1 := sqrt1_cases.mp ‹Sqrt1 b›
    match this with
    | Or.inl (_ : b ≃ 1) => calc
      a     ≃ _ := Rel.symm AA.identR
      a * 1 ≃ _ := AA.substR (Rel.symm ‹b ≃ 1›)
      a * b ≃ _ := ‹a * b ≃ 1›
      1     ≃ _ := Rel.symm ‹b ≃ 1›
      b     ≃ _ := Rel.refl
    | Or.inr (_ : b ≃ -1) => calc
      a             ≃ _ := Rel.symm neg_involutive
      (-(-a))       ≃ _ := AA.subst₁ (AA.subst₁ (Rel.symm AA.identR))
      (-(-(a * 1))) ≃ _ := AA.subst₁ AA.scompatR
      (-(a * -1))   ≃ _ := AA.subst₁ (AA.substR (Rel.symm ‹b ≃ -1›))
      (-(a * b))    ≃ _ := AA.subst₁ ‹a * b ≃ 1›
      (-1)          ≃ _ := Rel.symm ‹b ≃ -1›
      b             ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ b)
    show a * b ≃ 1
    calc
      a * b ≃ _ := AA.substL ‹a ≃ b›
      b * b ≃ _ := ‹Sqrt1 b›.elim
      1     ≃ _ := Rel.refl

/--
The product of two square roots of unity is minus one iff they are different.

**Property intuition**: It's an often-memorized algebraic fact that unlike
signs are the only ones whose product is negative.

**Proof intuition**: In the forward direction, assume the factors are the same
and use algebra to reach a contradiction. In the reverse direction, look at all
possible values for the factors. Eliminate the cases where they have the same
value using the assumption `a ≄ b`; show that the product is `-1` in the rest.
-/
theorem mul_sqrt1_neqv {a b : ℤ} [Sqrt1 a] [Sqrt1 b] : a * b ≃ -1 ↔ a ≄ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a * b ≃ -1) (_ : a ≃ b)
    show False
    have : (-1 : ℤ) ≃ 1 := calc
      (-1 : ℤ) ≃ _ := Rel.symm ‹a * b ≃ -1›
      a * b    ≃ _ := AA.substL ‹a ≃ b›
      b * b    ≃ _ := ‹Sqrt1 b›.elim
      1        ≃ _ := Rel.refl
    have : (-1 : ℤ) ≄ 1 := neg_one_neqv_one
    exact absurd ‹(-1 : ℤ) ≃ 1› ‹(-1 : ℤ) ≄ 1›
  case mpr =>
    intro (_ : a ≄ b)
    show a * b ≃ -1
    have a_cases : a ≃ 1 ∨ a ≃ -1 := sqrt1_cases.mp ‹Sqrt1 a›
    have b_cases : b ≃ 1 ∨ b ≃ -1 := sqrt1_cases.mp ‹Sqrt1 b›
    match a_cases with
    | Or.inl (_ : a ≃ 1) =>
      match b_cases with
      | Or.inl (_ : b ≃ 1) =>
        have : a ≃ b := Rel.trans ‹a ≃ 1› (Rel.symm ‹b ≃ 1›)
        exact absurd ‹a ≃ b› ‹a ≄ b›
      | Or.inr (_ : b ≃ -1) =>
        calc
          a * b ≃ _ := AA.substL ‹a ≃ 1›
          1 * b ≃ _ := AA.identL
          b     ≃ _ := ‹b ≃ -1›
          (-1)  ≃ _ := Rel.refl
    | Or.inr (_ : a ≃ -1) =>
      match b_cases with
      | Or.inl (_ : b ≃ 1) =>
        calc
          a * b ≃ _ := AA.substR ‹b ≃ 1›
          a * 1 ≃ _ := AA.identR
          a     ≃ _ := ‹a ≃ -1›
          (-1)  ≃ _ := Rel.refl
      | Or.inr (_ : b ≃ -1) =>
        have : a ≃ b := Rel.trans ‹a ≃ -1› (Rel.symm ‹b ≃ -1›)
        exact absurd ‹a ≃ b› ‹a ≄ b›

/--
Every `NonzeroWithSign` has a sign value that's either `1` or `-1`.

This is a lemma that's useful for the proof of `nonzero_iff_pos_or_neg`.

**Property and proof intuition**: We already know from `sqrt1_cases` that sign
values can only be `1` or `-1`. So this result just uses that fact to show what
the precise type of `NonzeroWithSign` is allowed to be.
-/
theorem nonzeroWithSign_cases
    {a s : ℤ} {sqrt1 : Sqrt1 s}
    : NonzeroWithSign a s → NonzeroWithSign a 1 ∨ NonzeroWithSign a (-1)
    := by
  intro (_ : NonzeroWithSign a s)
  show NonzeroWithSign a 1 ∨ NonzeroWithSign a (-1)
  have : s ≃ 1 ∨ s ≃ -1 := sqrt1_cases.mp ‹Sqrt1 s›
  match ‹s ≃ 1 ∨ s ≃ -1› with
  | Or.inl (_ : s ≃ 1) =>
    have : NonzeroWithSign a 1 :=
      NonzeroWithSign.subst_sign ‹s ≃ 1› ‹NonzeroWithSign a s›
    exact Or.inl ‹NonzeroWithSign a 1›
  | Or.inr (_ : s ≃ -1) =>
    have : NonzeroWithSign a (-1) :=
      NonzeroWithSign.subst_sign ‹s ≃ -1› ‹NonzeroWithSign a s›
    exact Or.inr ‹NonzeroWithSign a (-1)›

/--
All `Nonzero` representations of the same integer have the same sign.

**Property intuition**: From trichotomy, all nonzero integers are either
positive or negative, not both.

**Proof intuition**: Case split on all possible combinations of sign values. If
the signs are equal, we are done. Otherwise, the integer must be both
positive and negative, contradiction.
-/
theorem nonzeroWithSign_sign_inject
    {a s₁ s₂ : ℤ} {_ : Sqrt1 s₁} {_ : Sqrt1 s₂}
    : NonzeroWithSign a s₁ → NonzeroWithSign a s₂ → s₁ ≃ s₂
    := by
  intro (_ : NonzeroWithSign a s₁) (_ : NonzeroWithSign a s₂)
  show s₁ ≃ s₂
  have : s₁ ≃ 1 ∨ s₁ ≃ -1 := sqrt1_cases.mp ‹Sqrt1 s₁›
  have : s₂ ≃ 1 ∨ s₂ ≃ -1 := sqrt1_cases.mp ‹Sqrt1 s₂›
  have : s₁ ≃ s₂ ∨ (NonzeroWithSign a 1 ∧ NonzeroWithSign a (-1)) :=
    match ‹s₁ ≃ 1 ∨ s₁ ≃ -1› with
    | Or.inl (_ : s₁ ≃ 1) =>
      match ‹s₂ ≃ 1 ∨ s₂ ≃ -1› with
      | Or.inl (_ : s₂ ≃ 1) =>
        have : s₁ ≃ s₂ := Rel.trans ‹s₁ ≃ 1› (Rel.symm ‹s₂ ≃ 1›)
        Or.inl ‹s₁ ≃ s₂›
      | Or.inr (_ : s₂ ≃ -1) =>
        have : NonzeroWithSign a 1 :=
          NonzeroWithSign.subst_sign ‹s₁ ≃ 1› ‹NonzeroWithSign a s₁›
        have : NonzeroWithSign a (-1) :=
          NonzeroWithSign.subst_sign ‹s₂ ≃ -1› ‹NonzeroWithSign a s₂›
        Or.inr (And.intro ‹NonzeroWithSign a 1› ‹NonzeroWithSign a (-1)›)
    | Or.inr (_ : s₁ ≃ -1) =>
      match ‹s₂ ≃ 1 ∨ s₂ ≃ -1› with
      | Or.inl (_ : s₂ ≃ 1) =>
        have : NonzeroWithSign a (-1) :=
          NonzeroWithSign.subst_sign ‹s₁ ≃ -1› ‹NonzeroWithSign a s₁›
        have : NonzeroWithSign a 1 :=
          NonzeroWithSign.subst_sign ‹s₂ ≃ 1› ‹NonzeroWithSign a s₂›
        Or.inr (And.intro ‹NonzeroWithSign a 1› ‹NonzeroWithSign a (-1)›)
      | Or.inr (_ : s₂ ≃ -1) =>
        have : s₁ ≃ s₂ := Rel.trans ‹s₁ ≃ -1› (Rel.symm ‹s₂ ≃ -1›)
        Or.inl ‹s₁ ≃ s₂›
  match this with
  | Or.inl (_ : s₁ ≃ s₂) =>
    exact ‹s₁ ≃ s₂›
  | Or.inr (And.intro (_ : NonzeroWithSign a 1) (_ : NonzeroWithSign a (-1))) =>
    have : Positive a := positive_iff_sign_pos1.mpr ‹NonzeroWithSign a 1›
    have : Negative a := negative_iff_sign_neg1.mpr ‹NonzeroWithSign a (-1)›
    have : Positive a ∧ Negative a := And.intro ‹Positive a› ‹Negative a›
    exact absurd ‹Positive a ∧ Negative a› not_positive_and_negative

/-- Evidence that two integers have the same sign. -/
inductive SameSign (a b : ℤ) : Prop :=
| /--
  Create an instance of `SameSign`.

  **Parameters**:
  - `sign`: The sign value of `a` and `b`, as an integer.
  - `sqrt1`: Ensures that `sign` is a valid sign (i.e., has value `1` or `-1`).
  - `nwsa`: Evidence that `a` has sign `sign`.
  - `nwsb`: Evidence that `b` has sign `sign`.
  -/
  intro
    (sign : ℤ)
    (sqrt1 : Sqrt1 sign)
    (nwsa : NonzeroWithSign a sign)
    (nwsb : NonzeroWithSign b sign)

/--
Convenience constructor for `SameSign`.

Only needs the `NonzeroWithSign` arguments passed explicitly; the others are
inferred.
-/
def SameSign.mk
    {a b s : ℤ} [Sqrt1 s] (_ : NonzeroWithSign a s) (_ : NonzeroWithSign b s)
    : SameSign a b
    :=
  SameSign.intro s ‹Sqrt1 s› ‹NonzeroWithSign a s› ‹NonzeroWithSign b s›

/--
If two integers have the same sign, and one is positive, the other _must_ be
positive.

**Proof intuition**: Expand all definitions; use properties of
`NonzeroWithSign`.
-/
theorem same_sign_positive
    {a b : ℤ} : SameSign a b → Positive a → Positive b
    := by
  intro (SameSign.intro (s : ℤ) (_ : Sqrt1 s) nwsa nwsb)
  have : NonzeroWithSign a s := nwsa
  have : NonzeroWithSign b s := nwsb
  intro (_ : Positive a)
  show Positive b
  have : NonzeroWithSign a 1 := positive_iff_sign_pos1.mp ‹Positive a›
  have : s ≃ 1 :=
    nonzeroWithSign_sign_inject ‹NonzeroWithSign a s› ‹NonzeroWithSign a 1›
  have : NonzeroWithSign b 1 :=
    NonzeroWithSign.subst_sign ‹s ≃ 1› ‹NonzeroWithSign b s›
  have : Positive b := positive_iff_sign_pos1.mpr ‹NonzeroWithSign b 1›
  exact this

/--
Nonzero integers are either, and only, positive or negative.

**Property intuition**: If an integer is not zero, then by trichotomy, it must
be either positive or negative.

**Proof intuition**: Converts `Nonzero`, `Positive`, and `Negative` to and from
their `NonzeroWithSign` representations via `nonzeroWithSign_cases`,
`positive_iff_sign_pos1`, and `negative_iff_sign_neg1`.
-/
theorem nonzero_iff_pos_or_neg
    {a : ℤ} : Nonzero a ↔ Positive a ∨ Negative a
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Nonzero a)
    show Positive a ∨ Negative a
    have (Nonzero.intro (s : ℤ) (_ : Sqrt1 s) nwsa) := ‹Nonzero a›
    have : NonzeroWithSign a s := nwsa
    have : NonzeroWithSign a 1 ∨ NonzeroWithSign a (-1) :=
      nonzeroWithSign_cases ‹NonzeroWithSign a s›
    match ‹NonzeroWithSign a 1 ∨ NonzeroWithSign a (-1)› with
    | Or.inl (_ : NonzeroWithSign a 1) =>
      have : Positive a := positive_iff_sign_pos1.mpr ‹NonzeroWithSign a 1›
      exact Or.inl ‹Positive a›
    | Or.inr (_ : NonzeroWithSign a (-1)) =>
      have : Negative a := negative_iff_sign_neg1.mpr ‹NonzeroWithSign a (-1)›
      exact Or.inr ‹Negative a›
  case mpr =>
    intro (_ : Positive a ∨ Negative a)
    show Nonzero a
    match ‹Positive a ∨ Negative a› with
    | Or.inl (_ : Positive a) =>
      have : NonzeroWithSign a 1 := positive_iff_sign_pos1.mp ‹Positive a›
      exact Nonzero.mk ‹NonzeroWithSign a 1›
    | Or.inr (_ : Negative a) =>
      have : NonzeroWithSign a (-1) := negative_iff_sign_neg1.mp ‹Negative a›
      exact Nonzero.mk ‹NonzeroWithSign a (-1)›

/-- Integers meet all the requirements of a signed type. -/
instance signed : Signed ℤ := {
  positive_substitutive := { subst₁ := positive_subst }
  negative_substitutive := { subst₁ := negative_subst }
  trichotomy := sign_trichotomy
  nonzero_iff_pos_or_neg :=
    Relation.iff_trans nonzero_iff_nonzero_impl nonzero_iff_pos_or_neg
}

/--
A positive integer is a nonzero integer.

**Property and proof intuition**: This follows immediately from the theorem
that an integer is nonzero iff it is positive or negative.
-/
theorem nonzero_from_positive {a : ℤ} : Positive a → Nonzero a := by
  intro (_ : Positive a)
  show Nonzero a
  have : Positive a ∨ Negative a := Or.inl ‹Positive a›
  have : Nonzero a := nonzero_iff_pos_or_neg.mpr this
  exact this

/-- Instance version of `nonzero_from_positive`. -/
instance nonzero_from_positive_inst {a : ℤ} [AP (Positive a)] : Nonzero a :=
  nonzero_from_positive ‹AP (Positive a)›.ev

/--
Provide evidence that an integer is equivalent, or not equivalent, to zero.

**Property and proof intuition**: We already know from trichotomy of integers
that every integer is either zero, positive, or negative, and never more than
one of those at the same time. Combine the positive and negative categories to
obtain this result.
-/
theorem zero? (a : ℤ) : AA.ExactlyOneOfTwo (a ≃ 0) (Nonzero a) := by
  have tri : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a) :=
    Signed.trichotomy a
  apply And.intro
  case left =>
    show a ≃ 0 ∨ Nonzero a
    match tri.atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | AA.OneOfThree.second (_ : Positive a) =>
      have : Nonzero a := nonzero_iff_pos_or_neg.mpr (Or.inl ‹Positive a›)
      exact Or.inr ‹Nonzero a›
    | AA.OneOfThree.third (_ : Negative a) =>
      have : Nonzero a := nonzero_iff_pos_or_neg.mpr (Or.inr ‹Negative a›)
      exact Or.inr ‹Nonzero a›
  case right =>
    intro (And.intro (_ : a ≃ 0) (_ : Nonzero a))
    show False
    apply tri.atMostOne
    show AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a)
    have : Positive a ∨ Negative a := nonzero_iff_pos_or_neg.mp ‹Nonzero a›
    match ‹Positive a ∨ Negative a› with
    | Or.inl (_ : Positive a) =>
      exact AA.TwoOfThree.oneAndTwo ‹a ≃ 0› ‹Positive a›
    | Or.inr (_ : Negative a) =>
      exact AA.TwoOfThree.oneAndThree ‹a ≃ 0› ‹Negative a›

/--
The predicates `Nonzero` and `· ≄ 0` are equivalent characterizations of
integers.

**Proof intuition**: A simple corollary of
`AA.ExactlyOneOfTwo (a ≃ 0) (Nonzero a)`.
-/
theorem nonzero_iff_neqv_zero {a : ℤ} : Nonzero a ↔ a ≄ 0 := by
  have (And.intro (_ : a ≃ 0 ∨ Nonzero a) (_ : ¬(a ≃ 0 ∧ Nonzero a))) :=
    zero? a
  apply Iff.intro
  case mp =>
    intro (_ : Nonzero a) (_ : a ≃ 0)
    show False
    have : a ≃ 0 ∧ Nonzero a := And.intro ‹a ≃ 0› ‹Nonzero a›
    exact absurd ‹a ≃ 0 ∧ Nonzero a› ‹¬(a ≃ 0 ∧ Nonzero a)›
  case mpr =>
    intro (_ : a ≄ 0)
    show Nonzero a
    match ‹a ≃ 0 ∨ Nonzero a› with
    | Or.inl (_ : a ≃ 0) =>
      exact absurd ‹a ≃ 0› ‹a ≄ 0›
    | Or.inr (_ : Nonzero a) =>
      exact ‹Nonzero a›

/--
For a product of integers to be zero, at least one of its factors must be zero.

**Property and proof intuition**: This property alone is not very intuitive, or
at least the forward direction isn't. But eliminating the obvious cases where
either `a` or `b` are zero reduces the problem to showing that if `a` and `b`
are both nonzero, then their product must be nonzero as well. And that has some
intuitive justification; see `mul_preserves_nonzero`.
-/
theorem mul_split_zero {a b : ℤ} : a * b ≃ 0 ↔ a ≃ 0 ∨ b ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * b ≃ 0)
    show a ≃ 0 ∨ b ≃ 0
    have : a ≃ 0 ∨ Nonzero a := (zero? a).left
    match ‹a ≃ 0 ∨ Nonzero a› with
    | Or.inl (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | Or.inr (_ : Nonzero a) =>
      have : b ≃ 0 ∨ Nonzero b := (zero? b).left
      match ‹b ≃ 0 ∨ Nonzero b› with
      | Or.inl (_ : b ≃ 0) =>
        exact Or.inr ‹b ≃ 0›
      | Or.inr (_ : Nonzero b) =>
        apply False.elim
        show False
        have : ¬ (a * b ≃ 0 ∧ Nonzero (a * b)) := (zero? (a * b)).right
        apply this
        show a * b ≃ 0 ∧ Nonzero (a * b)
        apply And.intro
        · exact ‹a * b ≃ 0›
        · exact mul_preserves_nonzero ‹Nonzero a› ‹Nonzero b›
  case mpr =>
    intro (_ : a ≃ 0 ∨ b ≃ 0)
    show a * b ≃ 0
    match ‹a ≃ 0 ∨ b ≃ 0› with
    | Or.inl (_ : a ≃ 0) => calc
      a * b ≃ _ := AA.substL ‹a ≃ 0›
      0 * b ≃ _ := AA.absorbL
      0     ≃ _ := Rel.refl
    | Or.inr (_ : b ≃ 0) => calc
      a * b ≃ _ := AA.substR ‹b ≃ 0›
      a * 0 ≃ _ := AA.absorbR
      0     ≃ _ := Rel.refl

/--
If a product of integers is nonzero, then both factors must be nonzero.

**Property and proof intuition**: This follows immediately from the
contrapositive of the zero product property (`a ≃ 0 ∨ b ≃ 0 → a * b ≃ 0`).
-/
theorem nonzero_factors_if_nonzero_product
    {a b : ℤ} : Nonzero (a * b) → Nonzero a ∧ Nonzero b
    := by
  intro (_ : Nonzero (a * b))
  show Nonzero a ∧ Nonzero b
  have : a * b ≄ 0 := nonzero_iff_neqv_zero.mp ‹Nonzero (a * b)›
  have : ¬(a ≃ 0 ∨ b ≃ 0) := mt mul_split_zero.mpr ‹a * b ≄ 0›
  have (And.intro (_ : a ≄ 0) (_ : b ≄ 0)) :=
    Logic.not_or_iff_and_not.mp ‹¬(a ≃ 0 ∨ b ≃ 0)›
  have : Nonzero a := nonzero_iff_neqv_zero.mpr ‹a ≄ 0›
  have : Nonzero b := nonzero_iff_neqv_zero.mpr ‹b ≄ 0›
  exact And.intro ‹Nonzero a› ‹Nonzero b›

/--
The product of two integers is positive if and only if they have the same sign.

**Property intuition**: This really boils down to `1 * 1` and `-1 * -1` being
the only products of signs that result in `1`.

**Proof intuition**: The forward direction splits the product into its two
nonzero factors, and then accounts for all possible combinations of their
signs. The reverse direction follows easily from the fact that a sign squared
is always `1`.
-/
theorem positive_mul_iff_same_sign
    {a b : ℤ} : Positive (a * b) ↔ SameSign a b
    := by
  let ab := a * b
  apply Iff.intro
  case mp =>
    intro (_ : Positive ab)
    show SameSign a b
    have : Nonzero ab := nonzero_iff_pos_or_neg.mpr (Or.inl ‹Positive ab›)
    have (And.intro (_ : Nonzero a) (_ : Nonzero b)) :=
      nonzero_factors_if_nonzero_product ‹Nonzero ab›
    have (Nonzero.intro (sa : ℤ) (_ : Sqrt1 sa) nwsa) := ‹Nonzero a›
    have (Nonzero.intro (sb : ℤ) (_ : Sqrt1 sb) nwsb) := ‹Nonzero b›
    have : NonzeroWithSign a sa := nwsa
    have : NonzeroWithSign b sb := nwsb
    have nwsac : NonzeroWithSign a 1 ∨ NonzeroWithSign a (-1)
      := nonzeroWithSign_cases ‹NonzeroWithSign a sa›
    have nwsbc : NonzeroWithSign b 1 ∨ NonzeroWithSign b (-1)
      := nonzeroWithSign_cases ‹NonzeroWithSign b sb›
    have : SameSign a b ∨ NonzeroWithSign ab (-1) := match nwsac with
    | Or.inl (nwsa : NonzeroWithSign a 1) =>
      match nwsbc with
      | Or.inl (nwsb : NonzeroWithSign b 1) =>
        Or.inl (SameSign.mk nwsa nwsb)
      | Or.inr (nwsb : NonzeroWithSign b (-1)) =>
        have : NonzeroWithSign ab (1 * -1) :=
          mul_preserves_nonzeroWithSign nwsa nwsb
        have : NonzeroWithSign ab (-1) :=
          NonzeroWithSign.subst_sign AA.identL ‹NonzeroWithSign ab (1 * -1)›
        Or.inr ‹NonzeroWithSign ab (-1)›
    | Or.inr (nwsa : NonzeroWithSign a (-1)) =>
      match nwsbc with
      | Or.inl (nwsb : NonzeroWithSign b 1) =>
        have : NonzeroWithSign ab (-1 * 1) :=
          mul_preserves_nonzeroWithSign nwsa nwsb
        have : NonzeroWithSign ab (-1) :=
          NonzeroWithSign.subst_sign AA.identR ‹NonzeroWithSign ab (-1 * 1)›
        Or.inr ‹NonzeroWithSign ab (-1)›
      | Or.inr (nwsb : NonzeroWithSign b (-1)) =>
        Or.inl (SameSign.mk nwsa nwsb)
    match ‹SameSign a b ∨ NonzeroWithSign ab (-1)› with
    | Or.inl (_ : SameSign a b) =>
      exact ‹SameSign a b›
    | Or.inr (_ : NonzeroWithSign ab (-1)) =>
      have : Negative ab :=
        negative_iff_sign_neg1.mpr ‹NonzeroWithSign ab (-1)›
      have positive_and_negative : Positive ab ∧ Negative ab :=
        And.intro ‹Positive ab› ‹Negative ab›
      exact absurd positive_and_negative not_positive_and_negative
  case mpr =>
    intro (_ : SameSign a b)
    show Positive ab
    have (SameSign.intro (s : ℤ) (_ : Sqrt1 s) nwsa nwsb) := ‹SameSign a b›
    have : NonzeroWithSign a s := nwsa
    have : NonzeroWithSign b s := nwsb
    have : s * s ≃ 1 := ‹Sqrt1 s›.elim
    have : NonzeroWithSign ab (s * s) :=
      mul_preserves_nonzeroWithSign nwsa nwsb
    have : NonzeroWithSign ab 1 :=
      NonzeroWithSign.subst_sign ‹s * s ≃ 1› ‹NonzeroWithSign ab (s * s)›
    have : Positive ab := positive_iff_sign_pos1.mpr ‹NonzeroWithSign ab 1›
    exact this

/--
The sum of positive integers is positive.

**Property intuition**: Since this holds in the natural numbers, it must also
hold in the integers.

**Proof intuition**: Expand the definition of positive into equivalences of
integers to positive natural numbers, and show that adding them together gives
an equivalence that satisfies positivity.
-/
theorem add_preserves_positive
    {a b : ℤ} : Positive a → Positive b → Positive (a + b)
    := by
  intro (_ : Positive a) (_ : Positive b)
  show Positive (a + b)
  have (Exists.intro (n : ℕ) (And.intro (_ : Positive n) (_ : a ≃ coe n))) :=
    positive_elim_nat ‹Positive a›
  have (Exists.intro (m : ℕ) (And.intro (_ : Positive m) (_ : b ≃ coe m))) :=
    positive_elim_nat ‹Positive b›
  have : Positive (n + m) := Natural.positive_add ‹Positive n›
  have : a + b ≃ coe (n + m) := calc
    a + b         ≃ _ := AA.substL ‹a ≃ coe n›
    coe n + b     ≃ _ := AA.substR ‹b ≃ coe m›
    coe n + coe m ≃ _ := Rel.symm AA.compat₂
    coe (n + m)   ≃ _ := Rel.refl
  have : Positive (a + b) :=
    positive_intro_nat ‹Positive (n + m)› ‹a + b ≃ coe (n + m)›
  exact this

/--
The product of positive integers is positive.

**Property intuition**: Since this holds for natural numbers, it must hold for
integers as well.

**Proof intuition**: This is a corollary of the result that the product of
integers having the same sign is positive.
-/
theorem mul_preserves_positive
    {a b : ℤ} : Positive a → Positive b → Positive (a * b)
    := by
  intro (_ : Positive a) (_ : Positive b)
  show Positive (a * b)
  have : NonzeroWithSign a 1 := positive_iff_sign_pos1.mp ‹Positive a›
  have : NonzeroWithSign b 1 := positive_iff_sign_pos1.mp ‹Positive b›
  have : SameSign a b :=
    SameSign.mk ‹NonzeroWithSign a 1› ‹NonzeroWithSign b 1›
  have : Positive (a * b) := positive_mul_iff_same_sign.mpr ‹SameSign a b›
  exact this

/-- Instance version of `mul_preserves_positive`. -/
instance mul_preserves_positive_inst
    {a b : ℤ} [AP (Positive a)] [AP (Positive b)] : AP (Positive (a * b))
    := by
  have : Positive a := ‹AP (Positive a)›.ev
  have : Positive b := ‹AP (Positive b)›.ev
  have : Positive (a * b) := mul_preserves_positive ‹Positive a› ‹Positive b›
  exact AP.mk this

/--
The negations of positive values are negative.

**Proof intuition**: Convert to `NonzeroWithSign` and negate the sign operand.
-/
theorem positive_iff_negated_negative
    {a : ℤ} : Positive a ↔ Negative (-a)
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Positive a)
    show Negative (-a)
    have nwsa : NonzeroWithSign a 1 := positive_iff_sign_pos1.mp ‹Positive a›
    have : NonzeroWithSign a (-(-1)) :=
      NonzeroWithSign.subst_sign (Rel.symm neg_involutive) nwsa
    have : NonzeroWithSign (-a) (-1) :=
      nonzeroWithSign_swap_neg.mpr ‹NonzeroWithSign a (-(-1))›
    have : Negative (-a) :=
      negative_iff_sign_neg1.mpr ‹NonzeroWithSign (-a) (-1)›
    exact this
  case mpr =>
    intro (_ : Negative (-a))
    show Positive a
    have : NonzeroWithSign (-a) (-1) :=
      negative_iff_sign_neg1.mp ‹Negative (-a)›
    have : NonzeroWithSign a (-(-1)) :=
      nonzeroWithSign_swap_neg.mp ‹NonzeroWithSign (-a) (-1)›
    have : NonzeroWithSign a 1 :=
      NonzeroWithSign.subst_sign neg_involutive ‹NonzeroWithSign a (-(-1))›
    have : Positive a := positive_iff_sign_pos1.mpr ‹NonzeroWithSign a 1›
    exact this

/--
The negations of negative values are positive.

**Proof intuition**: Convert to `NonzeroWithSign` and negate the sign operand.
-/
theorem negative_iff_negated_positive
    {a : ℤ} : Negative a ↔ Positive (-a)
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Negative a)
    show Positive (-a)
    have : NonzeroWithSign a (-1) := negative_iff_sign_neg1.mp ‹Negative a›
    have : NonzeroWithSign (-a) 1 :=
      nonzeroWithSign_swap_neg.mpr ‹NonzeroWithSign a (-1)›
    have : Positive (-a) := positive_iff_sign_pos1.mpr ‹NonzeroWithSign (-a) 1›
    exact this
  case mpr =>
    intro (_ : Positive (-a))
    show Negative a
    have : NonzeroWithSign (-a) 1 := positive_iff_sign_pos1.mp ‹Positive (-a)›
    have : NonzeroWithSign a (-1) :=
      nonzeroWithSign_swap_neg.mp ‹NonzeroWithSign (-a) 1›
    have : Negative a := negative_iff_sign_neg1.mpr ‹NonzeroWithSign a (-1)›
    exact this

/--
Nonzero integers are exactly those whose sign values are square roots of unity.

**Property intuition**: Only zero has a sign value of zero, so all other
integers must have `1` or `-1`.

**Proof intuition**: Both directions split into positive and negative cases and
show that the property holds in either. It follows directly from the
definitions of square roots of unity and from the `sgn` of positive and
negative integers.
-/
theorem sgn_nonzero {a : ℤ} : Nonzero a ↔ Sqrt1 (sgn a) := by
  apply Iff.intro
  case mp =>
    intro (_ : Nonzero a)
    show Sqrt1 (sgn a)
    have : Positive a ∨ Negative a := nonzero_iff_pos_or_neg.mp ‹Nonzero a›
    match this with
    | Or.inl (_ : Positive a) =>
      have : 1 ≃ sgn a := Rel.symm (sgn_positive.mp ‹Positive a›)
      have : Sqrt1 1 := sqrt1_one (ℤ := ℤ)
      have : Sqrt1 (sgn a) := sqrt1_subst ‹1 ≃ sgn a› ‹Sqrt1 (1 : ℤ)›
      exact this
    | Or.inr (_ : Negative a) =>
      have : -1 ≃ sgn a := Rel.symm (sgn_negative.mp ‹Negative a›)
      have : Sqrt1 (-1) := sqrt1_neg_one (ℤ := ℤ)
      have : Sqrt1 (sgn a) := sqrt1_subst ‹-1 ≃ sgn a› ‹Sqrt1 (-1 : ℤ)›
      exact this
  case mpr =>
    intro (_ : Sqrt1 (sgn a))
    show Nonzero a
    have : sgn a ≃ 1 ∨ sgn a ≃ -1 := sqrt1_cases.mp ‹Sqrt1 (sgn a)›
    have : Positive a ∨ Negative a := match this with
    | Or.inl (_ : sgn a ≃ 1) =>
      have : Positive a := sgn_positive.mpr ‹sgn a ≃ 1›
      Or.inl this
    | Or.inr (_ : sgn a ≃ -1) =>
      have : Negative a := sgn_negative.mpr ‹sgn a ≃ -1›
      Or.inr this
    have : Nonzero a := nonzero_iff_pos_or_neg.mpr ‹Positive a ∨ Negative a›
    exact this

/--
A nonzero integer `a` can be written as the product of `sgn a` and a positive
natural number.

**Property intuition**: `NonzeroWithSign`'s sign parameter is exactly what the
`sgn` function was designed to find.

**Proof intuition**: A positive integer `a` has both `sgn a ≃ 1` and
`NonzeroWithSign a 1`. The result follows from substitution, and the same
applies for negative integers.
-/
theorem sgn_nonzeroWithSign
    {a : ℤ} [Sqrt1 (sgn a)] : NonzeroWithSign a (sgn a)
    := by
  have : sgn a ≃ 1 ∨ sgn a ≃ -1 := sqrt1_cases.mp ‹Sqrt1 (sgn a)›
  match this with
  | Or.inl (_ : sgn a ≃ 1) =>
    have : Positive a := sgn_positive.mpr ‹sgn a ≃ 1›
    have : NonzeroWithSign a 1 := positive_iff_sign_pos1.mp this
    have : NonzeroWithSign a (sgn a) :=
      NonzeroWithSign.subst_sign (Rel.symm ‹sgn a ≃ 1›) this
    exact this
  | Or.inr (_ : sgn a ≃ -1) =>
    have : Negative a := sgn_negative.mpr ‹sgn a ≃ -1›
    have : NonzeroWithSign a (-1) := negative_iff_sign_neg1.mp this
    have : NonzeroWithSign a (sgn a) :=
      NonzeroWithSign.subst_sign (Rel.symm ‹sgn a ≃ -1›) this
    exact this

/--
The `sgn` function respects equivalence of integers.

**Property intuition**: This must be the case for `sgn` to be useful.

**Proof intuition**: The value `a₁` is either zero, positive, or negative. In
each case, `a₂` must have the same property because it's equivalent to `a₁`.
But the result of `sgn` only depends on those properties, so `sgn a₁` and
`sgn a₂` must have the same value.
-/
theorem sgn_subst {a₁ a₂ : ℤ} : a₁ ≃ a₂ → sgn a₁ ≃ sgn a₂ := by
  intro (_ : a₁ ≃ a₂)
  show sgn a₁ ≃ sgn a₂
  have : AA.OneOfThree (a₁ ≃ 0) (Positive a₁) (Negative a₁) :=
    (sign_trichotomy a₁).atLeastOne
  match this with
  | AA.OneOfThree.first (_ : a₁ ≃ 0) =>
    have : a₂ ≃ 0 := AA.substLFn ‹a₁ ≃ a₂› ‹a₁ ≃ 0›
    calc
      sgn a₁ ≃ _ := sgn_zero.mp ‹a₁ ≃ 0›
      0      ≃ _ := Rel.symm (sgn_zero.mp ‹a₂ ≃ 0›)
      sgn a₂ ≃ _ := Rel.refl
  | AA.OneOfThree.second (_ : Positive a₁) =>
    have : Positive a₂ := positive_subst ‹a₁ ≃ a₂› ‹Positive a₁›
    calc
      sgn a₁ ≃ _ := sgn_positive.mp ‹Positive a₁›
      1      ≃ _ := Rel.symm (sgn_positive.mp ‹Positive a₂›)
      sgn a₂ ≃ _ := Rel.refl
  | AA.OneOfThree.third (_ : Negative a₁) =>
    have : Negative a₂ := negative_subst ‹a₁ ≃ a₂› ‹Negative a₁›
    calc
      sgn a₁ ≃ _ := sgn_negative.mp ‹Negative a₁›
      (-1)   ≃ _ := Rel.symm (sgn_negative.mp ‹Negative a₂›)
      sgn a₂ ≃ _ := Rel.refl

/--
The `sgn` function is idempotent.

**Property intuition**: The `sgn` function returns a canonical representative
of the states zero, positive, and negative. The sign value of this
representative is of course the same number.

**Proof intuition**: Split `a` into zero, positive, and negative states. Use
the definition of `sgn` and its substitutive property to show that `sgn a` and
`sgn (sgn a)` give the same result in each case.
-/
theorem sgn_idemp {a : ℤ} : sgn (sgn a) ≃ sgn a := by
  have : AA.OneOfThree (a ≃ 0) (Positive a) (Negative a) :=
    (sign_trichotomy a).atLeastOne
  match this with
  | AA.OneOfThree.first (_ : a ≃ 0) =>
    have : sgn a ≃ 0 := sgn_zero.mp ‹a ≃ 0›
    calc
      sgn (sgn a) ≃ _ := sgn_subst ‹sgn a ≃ 0›
      sgn (0 : ℤ) ≃ _ := sgn_subst (Rel.symm ‹a ≃ 0›)
      sgn a       ≃ _ := Rel.refl
  | AA.OneOfThree.second (_ : Positive a) =>
    have : sgn a ≃ 1 := sgn_positive.mp ‹Positive a›
    calc
      sgn (sgn a) ≃ _ := sgn_subst ‹sgn a ≃ 1›
      sgn (1 : ℤ) ≃ _ := sgn_positive.mp one_positive
      1           ≃ _ := Rel.symm ‹sgn a ≃ 1›
      sgn a       ≃ _ := Rel.refl
  | AA.OneOfThree.third (_ : Negative a) =>
    have : sgn a ≃ -1 := sgn_negative.mp ‹Negative a›
    calc
      sgn (sgn a)  ≃ _ := sgn_subst ‹sgn a ≃ -1›
      sgn (-1 : ℤ) ≃ _ := sgn_negative.mp neg_one_negative
      (-1)         ≃ _ := Rel.symm ‹sgn a ≃ -1›
      sgn a        ≃ _ := Rel.refl

/--
Both factors in a nonzero product have sign values that are square roots of
unity.

This is a useful lemma for the proof of `sgn_compat_mul`.

**Property and proof intuition**: Follows directly from nonzero products having
nonzero factors, and nonzero integers having square roots of unity as sign
values.
-/
theorem sqrt1_sgn_split_nonzero_mul
    {a b : ℤ} : Nonzero (a * b) → Sqrt1 (sgn a) ∧ Sqrt1 (sgn b)
    := by
  intro (_ : Nonzero (a * b))
  show Sqrt1 (sgn a) ∧ (Sqrt1 (sgn b))
  have (And.intro (_ : Nonzero a) (_ : Nonzero b)) :=
    nonzero_factors_if_nonzero_product ‹Nonzero (a * b)›
  have : Sqrt1 (sgn a) := sgn_nonzero.mp ‹Nonzero a›
  have : Sqrt1 (sgn b) := sgn_nonzero.mp ‹Nonzero b›
  exact And.intro ‹Sqrt1 (sgn a)› ‹Sqrt1 (sgn b)›

/--
The sign value of the product of two integers that each have square roots of
unity as sign values, is the product of those sign values.

This is a useful lemma for the proof of `sgn_compat_mul`.

**Property and proof intuition**: Follows directly from the sign value of
`NonzeroWithSign` being `sgn a`, and `NonzeroWithSign` being preserved under
multiplication.
-/
theorem nonzeroWithSign_mul_from_sqrt1_sgn
    {a b : ℤ} [Sqrt1 (sgn a)] [Sqrt1 (sgn b)]
    : NonzeroWithSign (a * b) (sgn a * sgn b)
    := by
  have nws_a : NonzeroWithSign a (sgn a) := sgn_nonzeroWithSign
  have nws_b : NonzeroWithSign b (sgn b) := sgn_nonzeroWithSign
  have : NonzeroWithSign (a * b) (sgn a * sgn b) :=
    mul_preserves_nonzeroWithSign nws_a nws_b
  exact this

/--
The product of nonzero integers with the same sign is positive, and likewise
the factors of a positive product must have the same sign.

**Property intuition**: This is one of the essential properties of any signed
number system; our intuition for it usually comes from having memorized it in
school.

**Proof intuition**: Follows directly from the property that the product of two
square roots of unity is one iff they are the same.
-/
theorem positive_mul_iff_sgn_eqv
    {a b : ℤ} [Nonzero (a * b)] : Positive (a * b) ↔ sgn a ≃ sgn b
    := by
  have (And.intro (_ : Sqrt1 (sgn a)) (_ : Sqrt1 (sgn b))) :=
    sqrt1_sgn_split_nonzero_mul ‹Nonzero (a * b)›
  have nws_ab_sgn : NonzeroWithSign (a * b) (sgn a * sgn b) :=
    nonzeroWithSign_mul_from_sqrt1_sgn
  apply Iff.intro
  case mp =>
    intro (_ : Positive (a * b))
    show sgn a ≃ sgn b
    have nws_ab_one : NonzeroWithSign (a * b) 1 :=
      positive_iff_sign_pos1.mp ‹Positive (a * b)›
    have : sgn a * sgn b ≃ 1 :=
      nonzeroWithSign_sign_inject nws_ab_sgn nws_ab_one
    have : sgn a ≃ sgn b := mul_sqrt1_eqv.mp this
    exact this
  case mpr =>
    intro (_ : sgn a ≃ sgn b)
    show Positive (a * b)
    have : sgn a * sgn b ≃ 1 := mul_sqrt1_eqv.mpr ‹sgn a ≃ sgn b›
    have : NonzeroWithSign (a * b) 1 :=
      NonzeroWithSign.subst_sign ‹sgn a * sgn b ≃ 1› nws_ab_sgn
    have : Positive (a * b) := positive_iff_sign_pos1.mpr this
    exact this

/--
The product of nonzero integers with different signs is negative, and likewise
the factors of a negative product must have different signs.

**Property intuition**: This is one of the essential properties of any signed
number system; our intuition for it usually comes from having memorized it in
school.

**Proof intuition**: Follows directly from the property that the product of two
square roots of unity is negative one iff they are different.
-/
theorem negative_mul_iff_sgn_neqv
    {a b : ℤ} [Nonzero (a * b)] : Negative (a * b) ↔ sgn a ≄ sgn b
    := by
  apply Iff.intro
  case mp =>
    intro (_ : Negative (a * b)) (_ : sgn a ≃ sgn b)
    show False
    have : Positive (a * b) := positive_mul_iff_sgn_eqv.mpr ‹sgn a ≃ sgn b›
    have both : Positive (a * b) ∧ Negative (a * b) :=
      And.intro this ‹Negative (a * b)›
    have not_both : ¬(Positive (a * b) ∧ Negative (a * b)) :=
      not_positive_and_negative
    exact absurd both not_both
  case mpr =>
    intro (_ : sgn a ≄ sgn b)
    show Negative (a * b)
    have (And.intro (_ : Sqrt1 (sgn a)) (_ : Sqrt1 (sgn b))) :=
      sqrt1_sgn_split_nonzero_mul ‹Nonzero (a * b)›
    have nws_ab : NonzeroWithSign (a * b) (sgn a * sgn b) :=
      nonzeroWithSign_mul_from_sqrt1_sgn
    have : sgn a * sgn b ≃ -1 := mul_sqrt1_neqv.mpr ‹sgn a ≄ sgn b›
    have : NonzeroWithSign (a * b) (-1) :=
      NonzeroWithSign.subst_sign this nws_ab
    have : Negative (a * b) := negative_iff_sign_neg1.mpr this
    exact this

/--
The `sgn` of any product of integers is the product of their `sgn`s.

This algebraic fact is very useful for working with `sgn`.

**Property intuition**: This is usually known as a few separate properties: the
product of like signs is positive, unlike signs negative, and zeros give zero.

**Proof intuition**: Split into zero, positive, and negative cases, and rely on
previous results to show the property holds in each.
-/
theorem sgn_compat_mul {a b : ℤ} : sgn (a * b) ≃ sgn a * sgn b := by
  have : a * b ≃ 0 ∨ Nonzero (a * b) := (zero? (a * b)).left
  match this with
  | Or.inl (_ : a * b ≃ 0) =>
    have : a ≃ 0 ∨ b ≃ 0 := mul_split_zero.mp ‹a * b ≃ 0›
    match this with
    | Or.inl (_ : a ≃ 0) =>
      calc
        sgn (a * b)   ≃ _ := sgn_zero.mp ‹a * b ≃ 0›
        0             ≃ _ := Rel.symm AA.absorbL
        0 * sgn b     ≃ _ := AA.substL (Rel.symm (sgn_zero.mp ‹a ≃ 0›))
        sgn a * sgn b ≃ _ := Rel.refl
    | Or.inr (_ : b ≃ 0) =>
      calc
        sgn (a * b)   ≃ _ := sgn_zero.mp ‹a * b ≃ 0›
        0             ≃ _ := Rel.symm AA.absorbR
        sgn a * 0     ≃ _ := AA.substR (Rel.symm (sgn_zero.mp ‹b ≃ 0›))
        sgn a * sgn b ≃ _ := Rel.refl
  | Or.inr (_ : Nonzero (a * b)) =>
    have (And.intro (_ : Sqrt1 (sgn a)) (_ : Sqrt1 (sgn b))) :=
      sqrt1_sgn_split_nonzero_mul ‹Nonzero (a * b)›
    have : Positive (a * b) ∨ Negative (a * b) :=
      nonzero_iff_pos_or_neg.mp ‹Nonzero (a * b)›
    match this with
    | Or.inl (_ : Positive (a * b)) =>
      have : sgn a ≃ sgn b := positive_mul_iff_sgn_eqv.mp ‹Positive (a * b)›
      calc
        sgn (a * b)   ≃ _ := sgn_positive.mp ‹Positive (a * b)›
        1             ≃ _ := Rel.symm (mul_sqrt1_eqv.mpr ‹sgn a ≃ sgn b›)
        sgn a * sgn b ≃ _ := Rel.refl
    | Or.inr (_ : Negative (a * b)) =>
      have : sgn a ≄ sgn b := negative_mul_iff_sgn_neqv.mp ‹Negative (a * b)›
      calc
        sgn (a * b)   ≃ _ := sgn_negative.mp ‹Negative (a * b)›
        (-1)          ≃ _ := Rel.symm (mul_sqrt1_neqv.mpr ‹sgn a ≄ sgn b›)
        sgn a * sgn b ≃ _ := Rel.refl

/--
Taking both the `sgn` and negation of an integer can be done in either order.

**Property intuition**: The two functions do independent things to their input
integers. The `sgn` function normalizes any integer into a sign value; the
negation function inverts the sign.

**Proof intuition**: Convert negation into multiplication by negative one, then
use compatibility of multiplication and `sgn`.
-/
theorem sgn_compat_neg {a : ℤ} : sgn (-a) ≃ -(sgn a) := calc
  sgn (-a)             ≃ _ := sgn_subst (Rel.symm mul_neg_one)
  sgn (-1 * a)         ≃ _ := sgn_compat_mul
  sgn (-1 : ℤ) * sgn a ≃ _ := AA.substL (sgn_negative.mp neg_one_negative)
  (-1) * sgn a         ≃ _ := mul_neg_one
  (-(sgn a))           ≃ _ := Rel.refl

/--
The product of a nonzero integer with its sign is always positive.

**Property intuition**: Mulplying a number by its sign does nothing for a
positive number, but it "cancels out" the negation of a negative number.

**Proof intuition**: Follows directly from algebraic properties of `sgn`.
-/
theorem positive_mul_sgn_self {a : ℤ} : Nonzero a → Positive (a * sgn a) := by
  intro (_ : Nonzero a)
  have : Sqrt1 (sgn a) := sgn_nonzero.mp ‹Nonzero a›
  have : sgn a * sgn a ≃ 1 := this.elim
  have : sgn (a * sgn a) ≃ 1 := calc
    sgn (a * sgn a)     ≃ _ := sgn_compat_mul
    sgn a * sgn (sgn a) ≃ _ := AA.substR sgn_idemp
    sgn a * sgn a       ≃ _ := ‹sgn a * sgn a ≃ 1›
    1                   ≃ _ := Rel.refl
  have : Positive (a * sgn a) := sgn_positive.mpr ‹sgn (a * sgn a) ≃ 1›
  exact this

/-- Instance version of `positive_mul_sgn_self`. -/
instance positive_mul_sgn_self_inst
    {a : ℤ} [Nonzero a] : AP (Positive (a * sgn a))
    :=
  AP.mk (positive_mul_sgn_self ‹Nonzero a›)

end Lean4Axiomatic.Integer
