import Lean4Axiomatic.Rational.Inverse

/-! # Rational numbers: sign -/

namespace Lean4Axiomatic.Rational

open Logic (AP)
open Signed (Negative Positive sgn)

/--
Operations pertaining to rational number signedness.

The operation names are prefixed with underscores so that they don't conflict
with the standard names. This allows the standard names to be used unqualified,
without a namespace prefix.
-/
class Sign.Ops
    {ℕ : outParam Type} [Natural ℕ] {ℤ : outParam Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
    :=
  /--
  The [_signum function_](https://en.wikipedia.org/wiki/Sign_function).

  Extracts the sign of a rational number.
  -/
  _sgn : ℚ → ℤ

  /-- Holds only for positive rational numbers. -/
  _Positive : ℚ → Prop

  /-- Holds only for negative rational numbers. -/
  _Negative : ℚ → Prop

/-- Enables the use of the standard name `sgn` for signum. -/
instance sgn_ops
    {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer ℤ] [Sign.Ops (ℤ := ℤ) ℚ]
    : Signed.Sgn.Ops (ℕ := ℕ) (ℤ := ℤ) ℚ
    := {
  sgn := Sign.Ops._sgn
}

/-- Enables the use of the standard names `Positive` and `Negative`. -/
instance signed_ops
    {ℕ ℤ : Type} [Natural ℕ] [Integer ℤ]
    {ℚ : Type} [Core.Ops (ℤ := ℤ) ℚ] [Sign.Ops (ℕ := ℕ) (ℤ := ℤ) ℚ]
    : Signed.Ops ℚ := {
  Positive := Sign.Ops._Positive
  Negative := Sign.Ops._Negative
  Nonzero := (· ≄ 0)
}

/-- Properties of rational number signedness. -/
class Sign.Props
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core.Ops (ℤ := ℤ) ℚ] [Multiplication.Ops ℚ] [Reciprocation.Ops ℚ]
      [Ops (ℤ := ℤ) ℚ]
    :=
  /-- `sgn` respects rational number equivalence. -/
  sgn_subst {p₁ p₂ : ℚ} : p₁ ≃ p₂ → sgn p₁ ≃ sgn p₂

  /-- Converting integers to rational numbers preserves their sign. -/
  sgn_from_integer {a : ℤ} : sgn (a : ℚ) ≃ Integer.sgn a

  /-- The `sgn` function is compatible with multiplication. -/
  sgn_compat_mul {p q : ℚ} : sgn (p * q) ≃ sgn p * sgn q

  /-- Taking the reciprocal of a rational number preserves its sign. -/
  sgn_recip {p : ℚ} [AP (p ≄ 0)] : sgn (p⁻¹) ≃ sgn p

  /-- A rational number is positive iff its sign is `1`. -/
  sgn_positive {p : ℚ} : Positive p ↔ sgn p ≃ 1

  /-- A rational number is negative iff its sign is `-1`. -/
  sgn_negative {p : ℚ} : Negative p ↔ sgn p ≃ -1

export Sign.Props (
  sgn_negative sgn_positive sgn_compat_mul sgn_from_integer sgn_recip sgn_subst
)

/-- All rational number sign axioms. -/
class Sign
    {ℕ : Type} [Natural ℕ] {ℤ : Type} [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type)
      [Core.Ops (ℤ := ℤ) ℚ] [Multiplication.Ops ℚ] [Reciprocation.Ops ℚ]
    :=
  toOps : Sign.Ops (ℤ := ℤ) ℚ
  toProps : Sign.Props ℚ
