import Lean4Axiomatic.Rational.Negation

/-! # Rational numbers: reciprocation and division -/

namespace Lean4Axiomatic.Rational

open Logic (AP)

/-- Operations pertaining to rational number reciprocation. -/
class Reciprocation.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    :=
  /-- Reciprocation of rational numbers. -/
  reciprocal (p : ℚ) [AP (p ≄ 0)] : ℚ

export Reciprocation.Ops (reciprocal)

/-- Enables the use of the `·⁻¹` operator for reciprocation. -/
postfix:120 "⁻¹" => reciprocal

/--
Implementation of floating-point notation for rational numbers.

The input parameters are specified by Lean's `OfScientific.ofScientific` class
and field.

**Intuition**: Let's define a value `expSign := if exponentIsNegative then -1
else 1`. Then this function computes
`mantissa * 10 ^ (expSign * decimalExponent)`. Exponentiation isn't defined for
rational numbers at this point, so we compute `10 ^ decimalExponent` in the
naturals and take its reciprocal if `exponentIsNegative`. This requires a proof
that `10 ^ decimalExponent` is never zero.
-/
def of_scientific
    {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation.Ops ℚ]
    (mantissa : Nat) (exponentIsNegative : Bool) (decimalExponent : Nat) : ℚ
    :=
  let naturalMantissa : ℕ := OfNat.ofNat mantissa
  let naturalDecimalExponent : ℕ := OfNat.ofNat decimalExponent
  let powTen := (10:ℕ) ^ naturalDecimalExponent

  have : (1:ℕ) ≄ 0 := Natural.one_neqv_zero
  have : AP ((1:ℕ) ≄ 0) := AP.mk this

  have : Natural.step 9 ≄ 0 := Natural.step_neqv_zero
  have : (10:ℕ) ≄ 0 := AA.neqv_substL (Rel.symm Natural.literal_step) this
  have : AP (powTen ≄ 0) := AP.mk (Natural.pow_preserves_nonzero_base this)
  let rationalPowTen : ℚ := if exponentIsNegative then powTen⁻¹ else powTen

  naturalMantissa * rationalPowTen

/--
Enables the use of scientific-notation literals for rational numbers.

It's given a higher default instance priority than the built-in `Float` type.
-/
@[default_instance mid+2]
instance of_scientific_inst
    {ℕ ℤ ℚ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation.Ops ℚ]
    : OfScientific ℚ
    := {
  ofScientific := of_scientific
}

/-- Properties of rational number reciprocation. -/
class Reciprocation.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Ops ℚ]
    :=
  /-- Reciprocation respects equivalence over its operand. -/
  recip_subst {p₁ p₂ : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → p₁⁻¹ ≃ p₂⁻¹

  /-- The reciprocal of a value is its left multiplicative inverse. -/
  mul_inverseL {p : ℚ} [AP (p ≄ 0)] : p⁻¹ * p ≃ 1

  /-- The reciprocal of a value is its right multiplicative inverse. -/
  mul_inverseR {p : ℚ} [AP (p ≄ 0)] : p * p⁻¹ ≃ 1

export Reciprocation.Props (mul_inverseL mul_inverseR recip_subst)

/-- All rational number reciprocation axioms. -/
class Reciprocation
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    :=
  toOps : Reciprocation.Ops ℚ
  toProps : Reciprocation.Props ℚ

attribute [instance] Reciprocation.toOps
attribute [instance] Reciprocation.toProps

/-- Operations pertaining to rational number division. -/
class Division.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ]
    :=
  /-- Division of rational numbers. -/
  div (p q : ℚ) [AP (q ≄ 0)] : ℚ

export Division.Ops (div)

/--
Enables the use of the `· / ·` operator for division.

We define the operator syntax directly here, instead of using the `Div` class
from the standard library. This is because our `div` operation has an extra
argument, an instance expressing that the divisor must be nonzero. The `Div`
class only provides a simple binary operation for its `div`.

Defined with high priority to avoid conflicts with `Div`'s syntax.
-/
infixl:70 (priority := high) " / " => div

/--
An inductive predicate expressing that a rational number can be represented as
a ratio of integers.

A value of `AsRatio p`, for some rational number `p`, is an existence proof
that there are two integers `a` and `b` whose ratio `a / b` is equivalent to
`p`.
-/
inductive AsRatio
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Division.Ops ℚ] (p : ℚ)
    : Prop
    :=
  /-- Construct a value of `AsRatio p`. -/
| intro
    (a b : ℤ)
    (b_nonzero : Integer.Nonzero b)
    (eqv_ratio : p ≃ a / b)

/-- Properties of rational number division. -/
class Division.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]
      [Ops ℚ]
    :=
  /--
  Division is equivalent to multiplication by the reciprocal of the second
  argument.
  -/
  div_mul_recip {p q : ℚ} [AP (q ≄ 0)] : p / q ≃ p * q⁻¹

  /--
  An induction/recursion principle for rationals.

  It states that any predicate (that is substitutive wrt `≃` on rationals) that
  holds for all rationals of the form `a / b` (where `a` and `b` are integers)
  will also hold for any rational. In particular, this implies that all
  rationals can be represented in the form `a / b`, which is formalized below
  in the theorem `as_ratio`. In other words, it excludes any rationals
  not of this form. This axiom is inspired by the
  [induction axiom](https://w.wiki/7hJp) of the Peano axioms.
  -/
  ind_fraction
    {motive : ℚ → Prop} [AA.Substitutive₁ (α := ℚ) motive (· ≃ ·) (· → ·)]
    : ((a b : ℤ) → [Integer.Nonzero b] → motive (a / b)) → (p : ℚ) → motive p

export Division.Props (div_mul_recip ind_fraction)

/-- All rational number division axioms. -/
class Division
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Reciprocation ℚ]
    :=
  toOps : Division.Ops ℚ
  toProps : Division.Props ℚ

attribute [instance] Division.toOps
attribute [instance] Division.toProps

/-! ## Derived properties -/

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
variable {ℚ : Type}
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
  [Negation ℚ] [Reciprocation ℚ] [Division ℚ]

/--
Equivalent to `Division.Props.ind_fraction` but with a more convenient argument
order when using the `apply` tactic.
-/
def ind_fraction_on
    {motive : ℚ → Prop}
    [AA.Substitutive₁ (α := ℚ) motive (· ≃ ·) (· → ·)] (p : ℚ)
    (on_int_frac : (a b : ℤ) → [Integer.Nonzero b] → motive ((a:ℚ) / b))
    : motive p
    :=
  ind_fraction on_int_frac p

/--
The predicate AsRatio satisfies a substitutive property with respect to the
equivalence relation `≃`.
I.e. if two rationals `a` and `b` are equivalent and `a` can be expressed as an
integer ratio, `a ≃ n / d`, then `b` can be expressed in the same way.
-/
theorem AsRatio_subst {a b : ℚ} : a ≃ b → AsRatio a → AsRatio b := by
  intro (_ : a ≃ b) (_ : AsRatio a)
  -- Decompose `a` into a ratio of integers
  have (AsRatio.intro (n : ℤ) (d : ℤ) (_ : Integer.Nonzero d) eqv)
    := ‹AsRatio a›
  have : a ≃ n / d := eqv
  have : b ≃ n / d := calc
    _ ≃ b     := eqv_refl
    _ ≃ a     := eqv_symm ‹a ≃ b›
    _ ≃ n / d := ‹a ≃ n / d›
  exact AsRatio.intro n d ‹Integer.Nonzero d› ‹b ≃ n / d›

instance AsRatio_subst_inst
    : AA.Substitutive₁ (α := ℚ) AsRatio (· ≃ ·) (· → ·)
    := {
  subst₁ := AsRatio_subst
}

  /--
  Every rational number can be expressed as a ratio of integers.

  Given any two integers, we can easily make a rational number; convert both of
  them to rationals using `from_integer`, then divide them. This theorem tells us
  that we can also do the reverse: given any rational, there are two integers
  that produce it when put into a ratio.

  It's a useful property because it provides a way to "deconstruct" a rational
  number into simpler pieces, which may be easier to work with. Although, it's
  preferable to work with rational numbers directly, and use this only when
  necessary.
  -/
theorem as_ratio (p : ℚ) : AsRatio p := by
  apply ind_fraction_on p
  intro (a : ℤ) (b : ℤ) (_ : Integer.Nonzero b)
  show AsRatio ((a:ℚ) / b)
  exact AsRatio.intro a b ‹Integer.Nonzero b› eqv_refl

/--
Square roots of unity are their own reciprocals.

**Property intuition**: Taking the reciprocal of a number doesn't change its
sign, and the only fraction that would be unchanged when flipping it is `1/1`,
i.e. the rational number `1`. Thus `1` and `-1` should be the only numbers to
satisfy this property.

**Proof intuition**: The defining proprty of square roots of unity,
`s * s ≃ 1`, is cruical for this proof because it introduces two factors of
`s`. One of them gets canceled by the reciprocal, leaving the other as the
result.
-/
theorem recip_sqrt1 {s : ℚ} [Sqrt1 s] : s⁻¹ ≃ s := calc
  s⁻¹           ≃ _ := eqv_symm mul_identL
  1 * s⁻¹       ≃ _ := mul_substL (eqv_symm ‹Sqrt1 s›.elim)
  (s * s) * s⁻¹ ≃ _ := mul_assoc
  s * (s * s⁻¹) ≃ _ := mul_substR mul_inverseR
  s * 1         ≃ _ := mul_identR
  s             ≃ _ := eqv_refl

/--
Division respects equivalence over its left operand.

**Property intuition**: Necessary for division to be a valid function on
rational numbers.

**Proof intuition**: The left operand of division is also the left operand of
the underlying multiplication, which is already known to obey the substitution
property.
-/
theorem div_substL {p₁ p₂ q : ℚ} [AP (q ≄ 0)] : p₁ ≃ p₂ → p₁ / q ≃ p₂ / q := by
  intro (_ : p₁ ≃ p₂)
  show p₁ / q ≃ p₂ / q
  calc
    p₁ / q   ≃ _ := div_mul_recip
    p₁ * q⁻¹ ≃ _ := mul_substL ‹p₁ ≃ p₂›
    p₂ * q⁻¹ ≃ _ := eqv_symm div_mul_recip
    p₂ / q   ≃ _ := eqv_refl

/--
Division respects equivalence over its right operand.

**Property intuition**: Necessary for division to be a valid function on
rational numbers.

**Proof intuition**: Division's right operand's reciprocal is the underlying
multiplication's right operand. Multiplication and reciprocation are already
known to obey the substitution property.
-/
theorem div_substR
    {p₁ p₂ q : ℚ} [AP (p₁ ≄ 0)] [AP (p₂ ≄ 0)] : p₁ ≃ p₂ → q / p₁ ≃ q / p₂
    := by
  intro (_ : p₁ ≃ p₂)
  show q / p₁ ≃ q / p₂
  calc
    q / p₁   ≃ _ := div_mul_recip
    q * p₁⁻¹ ≃ _ := mul_substR (recip_subst ‹p₁ ≃ p₂›)
    q * p₂⁻¹ ≃ _ := eqv_symm div_mul_recip
    q / p₂   ≃ _ := eqv_refl

/--
Dividing one by a rational number gives that number's reciprocal.

**Property intuition**: Multiplying `p` by `1/p` gives `1`, exactly the same as
multiplying by `p⁻¹`.

**Proof intuition**: Expand division into multiplication by reciprocal. The
factor of one disappears, leaving the result.
-/
theorem div_identL {p : ℚ} [AP (p ≄ 0)] : 1/p ≃ p⁻¹ := calc
  _ ≃ 1/p     := eqv_refl
  _ ≃ 1 * p⁻¹ := div_mul_recip
  _ ≃ p⁻¹     := mul_identL

/--
Dividing a rational number by one gives that number back.

**Property intuition**: Dividing a quantity into a single piece has no effect.

**Proof intuition**: Expand division into multiplication by reciprocal. The
reciprocal of one is one, which disappears, leaving the original number.
-/
theorem div_identR {p : ℚ} : p/1 ≃ p := calc
  _ ≃ p/1     := eqv_refl
  _ ≃ p * 1⁻¹ := div_mul_recip
  _ ≃ p * 1   := mul_substR recip_sqrt1
  _ ≃ p       := mul_identR

/--
Dividing a rational number by itself gives one.

**Property and proof intuition**: Self-division is equivalent to multiplication
by the reciprocal, which always gives one.
-/
theorem div_same {p : ℚ} [AP (p ≄ 0)] : p/p ≃ 1 := calc
  _ ≃ p/p     := eqv_refl
  _ ≃ p * p⁻¹ := div_mul_recip
  _ ≃ 1       := mul_inverseR

/--
Two rational numbers are equivalent if and only if their quotient is one.

**Property intuition**: A fraction with a numerator less than its denominator
is less than one; with a numerator greater than its denominator, greater than
one.

**Proof intuition**: The reverse direction trivially follows from `div_same`.
The forward direction uses the hypothesis `p/q ≃ 1` and the property
`q⁻¹ * q ≃ 1` to cancel out `p`, leaving `q` behind.
-/
theorem div_eqv_1 {p q : ℚ} [AP (q ≄ 0)] : p/q ≃ 1 ↔ p ≃ q := by
  apply Iff.intro
  case mp =>
    intro (_ : p/q ≃ 1)
    show p ≃ q
    calc
      _ ≃ p             := eqv_refl
      _ ≃ p * 1         := eqv_symm mul_identR
      _ ≃ p * (q⁻¹ * q) := mul_substR (eqv_symm mul_inverseL)
      _ ≃ (p * q⁻¹) * q := eqv_symm mul_assoc
      _ ≃ (p/q) * q     := mul_substL (eqv_symm div_mul_recip)
      _ ≃ 1 * q         := mul_substL ‹p/q ≃ 1›
      _ ≃ q             := mul_identL
  case mpr =>
    intro (_ : p ≃ q)
    show p/q ≃ 1
    calc
      _ ≃ p/q := eqv_refl
      _ ≃ q/q := div_substL ‹p ≃ q›
      _ ≃ 1   := div_same

/--
The reciprocal of a nonzero rational is itself nonzero.

**Property and proof intuition**: For `p * p⁻¹ ≃ 1` to hold, neither factor can
be zero.
-/
theorem recip_preserves_nonzero {p : ℚ} [AP (p ≄ 0)] : p⁻¹ ≄ 0 := by
  intro (_ : p⁻¹ ≃ 0)
  show False
  have : p ≃ 0 := calc
    _ ≃ p             := eqv_refl
    _ ≃ p * 1         := eqv_symm mul_identR
    _ ≃ p * (p * p⁻¹) := mul_substR (eqv_symm mul_inverseR)
    _ ≃ p * (p * 0)   := mul_substR (mul_substR ‹p⁻¹ ≃ 0›)
    _ ≃ p * 0         := mul_substR mul_absorbR
    _ ≃ 0             := mul_absorbR
  exact absurd ‹p ≃ 0› ‹AP (p ≄ 0)›.ev

/--
Instance equivalent of `recip_preserves_nonzero`.

Enables easy syntax for nested reciprocals, or reciprocals in denominators.
-/
instance recip_preserves_nonzero_inst
    {p : ℚ} [AP (p ≄ 0)] : AP (p⁻¹ ≄ 0)
    :=
  AP.mk recip_preserves_nonzero

/--
Double reciprocation is idempotent.

**Property intuition**: "Flipping over" a fraction twice brings back the
original fraction.

**Proof intuition**: Uses multiplicative inverse twice: first to introduce `p`
and `p⁻¹`, then to cancel `p⁻¹` and `(p⁻¹)⁻¹`, leaving `p` behind.
-/
theorem recip_idemp {p : ℚ} [AP (p ≄ 0)] : (p⁻¹)⁻¹ ≃ p := calc
  _ ≃ (p⁻¹)⁻¹             := eqv_refl
  _ ≃ 1 * (p⁻¹)⁻¹         := eqv_symm mul_identL
  _ ≃ (p * p⁻¹) * (p⁻¹)⁻¹ := mul_substL (eqv_symm mul_inverseR)
  _ ≃ p * (p⁻¹ * (p⁻¹)⁻¹) := mul_assoc
  _ ≃ p * 1               := mul_substR mul_inverseR
  _ ≃ p                   := mul_identR

end Lean4Axiomatic.Rational
