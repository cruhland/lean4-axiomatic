import Lean4Axiomatic.Rational.Exponentiation

/-! # Generic implementation of exponentiation to integers, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Lean4Axiomatic.Logic (AP)

variable
  {ℕ ℤ : Type} [Natural ℕ] [Natural.Induction.{1} ℕ] [Integer (ℕ := ℕ) ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]

def _pow (p : ℚ) (a : ℤ) [AP (p ≄ 0)] : ℚ :=
  rec_diff_on a (λ (n m : ℕ) => p^n / p^m)

/--
TODO

The constraint for `ℤ` to be an integer is needed to ensure that this doesn't
also generate an `Exponentiation.Ops ℚ ℕ`, hiding the `· ^ ·` operator for
natural number exponentiation.
-/
local instance exponentiation_ops : Exponentiation.Ops ℚ ℤ := {
  _pow := _pow
}

theorem pow_diff
    {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - (m:ℤ)) ≃ p^n / p^m
    := by
  let on_diff := λ (n m : ℕ) => p^n / p^m
  calc
    _ ≃ p^((n:ℤ) - (m:ℤ))                   := eqv_refl
    _ ≃ rec_diff_on ((n:ℤ) - (m:ℤ)) on_diff := eqv_refl
    _ = on_diff n m                         := rec_diff_on_eval
    _ ≃ p^n / p^m                           := eqv_refl

def exponentiation_props : Exponentiation.Props ℚ := {
  pow_diff := pow_diff
}

def exponentiation : Exponentiation ℚ := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Rational.Impl.Generic
