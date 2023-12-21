import Lean4Axiomatic.Rational.Exponentiation

/-! # Generic implementation of exponentiation to integers, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Lean4Axiomatic.Logic (AP)

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Integer.Induction.{1} ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]

def _pow_on_diff (p : ℚ) [AP (p ≄ 0)] (n m : ℕ) : ℚ := p^n / p^m

theorem _pow_on_diff_subst
    {p : ℚ} [AP (p ≄ 0)] {n₁ m₁ n₂ m₂ : ℕ} :
    (n₁:ℤ) - m₁ ≃ n₂ - m₂ → _pow_on_diff p n₁ m₁ ≃ _pow_on_diff p n₂ m₂
    := by
  intro (_ : (n₁:ℤ) - m₁ ≃ n₂ - m₂)
  show _pow_on_diff p n₁ m₁ ≃ _pow_on_diff p n₂ m₂

  have pow_add_n₁m₂ : p^n₁ * p^m₂ ≃ p^(n₁ + m₂) :=
    Rel.symm Natural.pow_compatL_add
  have pow_add_m₁n₂ : p^m₁ * p^n₂ ≃ p^(m₁ + n₂) :=
    Rel.symm Natural.pow_compatL_add

  have : (n₁:ℤ) + m₂ ≃ n₂ + m₁ :=
    Integer.sub_swap_add.mp ‹(n₁:ℤ) - m₁ ≃ n₂ - m₂›
  have : ((n₁ + m₂:ℕ):ℤ) ≃ ((m₁ + n₂:ℕ):ℤ) := calc
    _ = ((n₁ + m₂:ℕ):ℤ) := rfl
    _ ≃ (n₁:ℤ) + m₂     := AA.compat₂
    _ ≃ n₂ + m₁         := ‹(n₁:ℤ) + m₂ ≃ n₂ + m₁›
    _ ≃ m₁ + n₂         := AA.comm
    _ ≃ ((m₁ + n₂:ℕ):ℤ) := Rel.symm AA.compat₂
  have : n₁ + m₂ ≃ m₁ + n₂ := AA.inject this
  have pow_add_subst : p^(n₁ + m₂) ≃ p^(m₁ + n₂) := Natural.pow_substR this

  have : AP (_pow_on_diff p n₂ m₂ ≄ 0) := by
    have : AP (p^n₂ / p^m₂ ≄ 0) := inferInstance
    have : AP (_pow_on_diff p n₂ m₂ ≄ 0) := this
    exact this
  have : _pow_on_diff p n₁ m₁ / _pow_on_diff p n₂ m₂ ≃ 1 := calc
    _ = _pow_on_diff p n₁ m₁ / _pow_on_diff p n₂ m₂ := rfl
    _ = (p^n₁ / p^m₁) / (p^n₂ / p^m₂) := rfl
    _ ≃ (p^n₁ * p^m₂) / (p^m₁ * p^n₂) := div_div_div
    _ ≃ p^(n₁ + m₂) / (p^m₁ * p^n₂)   := div_substL pow_add_n₁m₂
    _ ≃ p^(n₁ + m₂) / p^(m₁ + n₂)     := div_substR pow_add_m₁n₂
    _ ≃ p^(m₁ + n₂) / p^(m₁ + n₂)     := div_substL pow_add_subst
    _ ≃ 1                             := div_same
  have : _pow_on_diff p n₁ m₁ ≃ _pow_on_diff p n₂ m₂ := div_eqv_1.mp this
  exact this

instance _pow_ind_diff_constraints
    {p : ℚ} [AP (p ≄ 0)] :
    Integer.Induction.ConstConstraints (ℤ := ℤ) (_pow_on_diff p)
    :=
  Integer.ind_constraints_const (X := ℚ) (_pow_on_diff_subst (p := p))

def _pow (p : ℚ) [AP (p ≄ 0)] (a : ℤ) : ℚ :=
  Integer.rec_diff_on a (_pow_on_diff p)

/--
TODO

The constraint for `ℤ` to be an integer is needed to ensure that this doesn't
also generate an `Exponentiation.Ops ℚ ℕ`, hiding the `· ^ ·` operator for
natural number exponentiation.
-/
local instance exponentiation_ops : Integer.Exponentiation.Ops ℚ ℤ := {
  _pow := _pow
}

theorem pow_diff
    {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - m) ≃ p^n / p^m
    := by
  let on_diff := _pow_on_diff p
  calc
    _ = p^((n:ℤ) - m)                           := rfl
    _ = Integer.rec_diff_on ((n:ℤ) - m) on_diff := rfl
    _ ≃ on_diff n m                             := Integer.rec_diff_on_eval
    _ = p^n / p^m                               := rfl

/-- TODO -/
theorem pow_substR
    {p : ℚ} [AP (p ≄ 0)] {a₁ a₂ : ℤ} : a₁ ≃ a₂ → p^a₁ ≃ p^a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show p^a₁ ≃ p^a₂
  let on_diff := _pow_on_diff p
  calc
    _ = p^a₁ := rfl
    _ = Integer.rec_diff_on a₁ on_diff := rfl
    _ ≃ Integer.rec_diff_on a₂ on_diff := Integer.rec_diff_on_subst ‹a₁ ≃ a₂›
    _ = p^a₂ := rfl

def exponentiation_props :
    Integer.Exponentiation.Props (α := ℚ) (ℤ := ℤ) (· * ·) (· / ·) := {
  pow_diff := pow_diff
  pow_substR := pow_substR
}

def integer_exponentiation :
    Integer.Exponentiation (α := ℚ) (ℤ := ℤ) (· * ·) (· / ·) := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Rational.Impl.Generic
